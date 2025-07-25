//! On-disk management of reference and test documents.
//!
//! These documents are currently stored as individual pages in the PNG format.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io;
use std::iter;
use std::path::Path;

use compile::TestWorldAdapter;
use compile::Warnings;
use ecow::EcoVec;
use thiserror::Error;
use tiny_skia::Pixmap;
use typst::diag::Warned;
use typst::layout::PagedDocument;
use typst::syntax::Source;
use typst::World;

use self::compare::Strategy;
use self::render::Origin;

pub mod compare;
pub mod compile;
pub mod render;

use crate::test::PageSelections;

/// The extension used in the page storage, each page is stored separately with it.
pub const PAGE_EXTENSION: &str = "png";

/// A document that was rendered from an in-memory compilation, or loaded from disk.
#[derive(Debug, Clone)]
pub struct Document {
    doc: Option<Box<PagedDocument>>,
    buffers: EcoVec<Pixmap>,
}

impl Document {
    /// Creates a new document from the given buffers.
    pub fn new<I: IntoIterator<Item = Pixmap>>(buffers: I) -> Self {
        Self {
            doc: None,
            buffers: buffers.into_iter().collect(),
        }
    }

    /// Compiles and renders a new document from the given source.
    pub fn compile<'w, F>(
        source: Source,
        world: &'w dyn World,
        pixel_per_pt: f32,
        warnings: Warnings,
        f: F,
    ) -> Warned<Result<Self, compile::Error>>
    where
        F: for<'a> FnOnce(&'a mut TestWorldAdapter<'w>) -> &'a mut TestWorldAdapter<'w>,
    {
        let Warned { output, warnings } = compile::compile(source, world, warnings, f);

        Warned {
            output: output.map(|doc| Self::render(doc, pixel_per_pt)),
            warnings,
        }
    }

    /// Creates a new rendered document from a compiled one.
    pub fn render<D: Into<Box<PagedDocument>>>(doc: D, pixel_per_pt: f32) -> Self {
        let doc = doc.into();

        let buffers = doc
            .pages
            .iter()
            .map(|page| typst_render::render(page, pixel_per_pt))
            .collect();

        Self {
            doc: Some(doc),
            buffers,
        }
    }

    /// Renders a diff from the given documents pixel buffers, the resulting new
    /// document will have no inner document set because it was created only
    /// from pixel buffers.
    ///
    /// Diff images are created pair-wise in order using [`render::page_diff`].
    pub fn render_diff(base: &Self, change: &Self, origin: Origin) -> Self {
        let buffers = iter::zip(&base.buffers, &change.buffers)
            .map(|(base, change)| render::page_diff(base, change, origin))
            .collect();

        Self { doc: None, buffers }
    }

    /// Collects the reference document in the given directory.
    #[tracing::instrument(skip_all, fields(dir = ?dir.as_ref()))]
    pub fn load<P: AsRef<Path>>(dir: P) -> Result<Self, LoadError> {
        let mut buffers = BTreeMap::new();

        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();

            if !entry.file_type()?.is_file() {
                tracing::trace!(entry = ?path, "ignoring non-file entry in reference directory");
                continue;
            }

            if path.extension().is_none()
                || path.extension().is_some_and(|ext| ext != PAGE_EXTENSION)
            {
                tracing::trace!(entry = ?path, "ignoring non-PNG entry in reference directory");
                continue;
            }

            let Some(page) = path
                .file_stem()
                .and_then(|s| s.to_str())
                .and_then(|s| s.parse().ok())
                .filter(|&num| num != 0)
            else {
                tracing::trace!(
                    entry = ?path,
                    "ignoring non-numeric or invalid filename in reference directory",
                );
                continue;
            };

            buffers.insert(page, Pixmap::load_png(path)?);
        }

        // Check we got pages starting at 1.
        match buffers.first_key_value() {
            Some((min, _)) if *min != 1 => {
                return Err(LoadError::MissingPages(buffers.into_keys().collect()));
            }
            Some(_) => {}
            None => {
                return Err(LoadError::MissingPages(buffers.into_keys().collect()));
            }
        }

        // Check we got pages ending in the page count.
        match buffers.last_key_value() {
            Some((max, _)) if *max != buffers.len() => {
                return Err(LoadError::MissingPages(buffers.into_keys().collect()));
            }
            Some(_) => {}
            None => {
                return Err(LoadError::MissingPages(buffers.into_keys().collect()));
            }
        }

        Ok(Self {
            doc: None,
            // NOTE(tinger): the pages are ordered by key and must not have any
            // page keys missing
            buffers: buffers.into_values().collect(),
        })
    }

    /// Saves a single page within the given directory with the given 1-based page
    /// number.
    ///
    /// # Panics
    /// Panics if `num == 0`.
    #[tracing::instrument(skip_all, fields(dir = ?dir.as_ref()))]
    pub fn save<P: AsRef<Path>>(
        &self,
        dir: P,
        optimize_options: Option<&oxipng::Options>,
    ) -> Result<(), SaveError> {
        tracing::trace!(?optimize_options, "using optimize options");

        for (num, page) in self
            .buffers
            .iter()
            .enumerate()
            .map(|(idx, page)| (idx + 1, page))
        {
            let path = dir
                .as_ref()
                .join(num.to_string())
                .with_extension(PAGE_EXTENSION);

            if let Some(options) = optimize_options {
                let buffer = page.encode_png()?;
                let optimized = oxipng::optimize_from_memory(&buffer, options)?;
                fs::write(path, optimized)?;
            } else {
                page.save_png(path)?;
            }
        }

        Ok(())
    }
}

impl Document {
    /// The inner document if this was created from an in-memory compilation.
    pub fn doc(&self) -> Option<&PagedDocument> {
        self.doc.as_deref()
    }

    /// The pixel buffers of the rendered pages in this document.
    pub fn buffers(&self) -> &[Pixmap] {
        &self.buffers
    }
}

impl Document {
    /// Compares two documents using the given strategy.
    ///
    /// Comparisons are created pair-wise in order using [`compare::page`].
    pub fn compare(
        outputs: &Self,
        references: &Self,
        strategy: Strategy,
        page_selections: Option<PageSelections>,
    ) -> Result<(), compare::Error> {
        let (page_errors, output_len, reference_len) = if let Some(page_selections) =
            page_selections
        {
            let outputs_filtered: Vec<_> = outputs
                .buffers
                .iter()
                .enumerate()
                .filter(|(i, _)| page_selections.contains(*i))
                .collect();
            let references_filtered: Vec<_> = references
                .buffers
                .iter()
                .enumerate()
                .filter(|(i, _)| page_selections.contains(*i))
                .collect();

            let errors = iter::zip(outputs_filtered.iter(), references_filtered.iter())
                .filter_map(|((idx, a), (_, b))| {
                    compare::page(a, b, strategy).err().map(|e| (*idx, e))
                })
                .collect::<Vec<_>>();

            (errors, outputs_filtered.len(), references_filtered.len())
        } else {
            let errors = iter::zip(&outputs.buffers, &references.buffers)
                .enumerate()
                .filter_map(|(idx, (a, b))| compare::page(a, b, strategy).err().map(|e| (idx, e)))
                .collect::<Vec<_>>();

            (errors, outputs.buffers.len(), references.buffers.len())
        };

        if !page_errors.is_empty() || output_len != reference_len {
            return Err(compare::Error {
                output: output_len,
                reference: reference_len,
                pages: page_errors,
            });
        }

        Ok(())
    }
}
/// Returned by [`Document::load`].
#[derive(Debug, Error)]
pub enum LoadError {
    /// One or more pages were missing, contains the physical page numbers which
    /// were found.
    #[error("one or more pages were missing, found: {0:?}")]
    MissingPages(BTreeSet<usize>),

    /// A page could not be decoded.
    #[error("a page could not be decoded")]
    Page(#[from] png::DecodingError),

    /// An io error occurred.
    #[error("an io error occurred")]
    Io(#[from] io::Error),
}

/// Returned by [`Document::save`].
#[derive(Debug, Error)]
pub enum SaveError {
    /// A page could not be optimized.
    #[error("a page could not be optimized")]
    Optimize(#[from] oxipng::PngError),

    /// A page could not be encoded.
    #[error("a page could not be encoded")]
    Page(#[from] png::EncodingError),

    /// An IO error occurred.
    #[error("an io error occurred")]
    Io(#[from] io::Error),
}

#[cfg(test)]
mod tests {
    use ecow::eco_vec;
    use tytanic_utils::fs::TempTestEnv;

    use super::*;
    use crate::doc::compare::PageError;

    #[test]
    fn test_document_save() {
        let doc = Document {
            doc: None,
            buffers: eco_vec![Pixmap::new(10, 10).unwrap(); 3],
        };

        TempTestEnv::run(
            |root| root,
            |root| {
                doc.save(root, None).unwrap();
            },
            |root| {
                root.expect_file_content("1.png", doc.buffers[0].encode_png().unwrap())
                    .expect_file_content("2.png", doc.buffers[1].encode_png().unwrap())
                    .expect_file_content("3.png", doc.buffers[2].encode_png().unwrap())
            },
        );
    }

    #[test]
    fn test_document_load() {
        let buffers = eco_vec![Pixmap::new(10, 10).unwrap(); 3];

        TempTestEnv::run_no_check(
            |root| {
                root.setup_file("1.png", buffers[0].encode_png().unwrap())
                    .setup_file("2.png", buffers[1].encode_png().unwrap())
                    .setup_file("3.png", buffers[2].encode_png().unwrap())
            },
            |root| {
                let doc = Document::load(root).unwrap();

                assert_eq!(doc.buffers[0], buffers[0]);
                assert_eq!(doc.buffers[1], buffers[1]);
                assert_eq!(doc.buffers[2], buffers[2]);
            },
        );
    }

    #[test]
    fn test_document_compare_with_page_range() {
        let mut output_buffers_vec = vec![Pixmap::new(10, 10).unwrap(); 5];
        output_buffers_vec[2] = Pixmap::new(12, 12).unwrap();
        let output_buffers = EcoVec::from(output_buffers_vec);

        let reference_buffers = eco_vec![Pixmap::new(10, 10).unwrap(); 5];

        let output = Document::new(output_buffers);
        let reference = Document::new(reference_buffers);

        // Test case 1: No page range, should fail on page 3
        let result = Document::compare(&output, &reference, Strategy::default(), None);
        assert!(matches!(
            result,
            Err(compare::Error {
                pages, ..
            }) if matches!(&pages[..], [(_, PageError::Dimensions { .. })])
        ));

        // Test case 2: Page range including the different page, should fail
        let selections = "1-3".parse::<PageSelections>().unwrap();
        let result = Document::compare(&output, &reference, Strategy::default(), Some(selections));
        assert!(matches!(
            result,
            Err(compare::Error {
                pages, ..
            }) if matches!(&pages[..], [(_, PageError::Dimensions { .. })])
        ));

        // Test case 3: Page range excluding the different page, should pass
        let selections = "1-2".parse::<PageSelections>().unwrap();
        assert!(
            Document::compare(&output, &reference, Strategy::default(), Some(selections)).is_ok()
        );

        // Test case 4: Page range for a single page that is different, should fail
        let selections = "3".parse::<PageSelections>().unwrap();
        let result = Document::compare(&output, &reference, Strategy::default(), Some(selections));
        assert!(matches!(
            result,
            Err(compare::Error {
                pages, ..
            }) if matches!(&pages[..], [(_, PageError::Dimensions { .. })])
        ));

        // Test case 5: Different page counts, should fail
        let reference_short = Document::new(eco_vec![Pixmap::new(10, 10).unwrap(); 4]);
        let result = Document::compare(&output, &reference_short, Strategy::default(), None);
        assert!(matches!(
            result,
            Err(compare::Error {
                output: 5,
                reference: 4,
                ..
            })
        ));
    }
}
