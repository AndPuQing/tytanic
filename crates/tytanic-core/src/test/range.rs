use std::num::NonZeroUsize;
use std::str::FromStr;

use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PageRange {
    pub start: NonZeroUsize,
    pub end: NonZeroUsize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PageSelection {
    Single(NonZeroUsize),
    Range(PageRange),
}

impl PageSelection {
    pub fn contains(&self, page_number: NonZeroUsize) -> bool {
        match self {
            PageSelection::Single(n) => *n == page_number,
            PageSelection::Range(range) => page_number >= range.start && page_number <= range.end,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PageSelections(pub Vec<PageSelection>);

impl PageSelections {
    pub fn contains(&self, page_index: usize) -> bool {
        let page_number = match NonZeroUsize::new(page_index + 1) {
            Some(n) => n,
            None => return false,
        };
        self.0.iter().any(|s| s.contains(page_number))
    }
}

#[derive(Debug, Error)]
pub enum ParsePageRangeError {
    #[error("page range cannot be empty")]
    Empty,

    #[error("invalid page number: {0}")]
    InvalidPage(String),

    #[error("invalid page range: {0}")]
    InvalidRange(String),
}

impl FromStr for PageSelections {
    type Err = ParsePageRangeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim().trim_matches('"');
        if s.is_empty() {
            return Err(ParsePageRangeError::Empty);
        }

        let mut selections = Vec::new();
        for part in s.split(',') {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }

            if let Some((start_str, end_str)) =
                part.split_once("..").or_else(|| part.split_once('-'))
            {
                let start = start_str
                    .trim()
                    .parse()
                    .map_err(|_| ParsePageRangeError::InvalidPage(start_str.to_string()))?;
                let end = end_str
                    .trim()
                    .parse()
                    .map_err(|_| ParsePageRangeError::InvalidPage(end_str.to_string()))?;
                selections.push(PageSelection::Range(PageRange { start, end }));
            } else {
                let page = part
                    .parse()
                    .map_err(|_| ParsePageRangeError::InvalidPage(part.to_string()))?;
                selections.push(PageSelection::Single(page));
            }
        }

        if selections.is_empty() {
            return Err(ParsePageRangeError::Empty);
        }

        Ok(PageSelections(selections))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_parse_page_selections() {
        // Test single page
        let selections = "5".parse::<PageSelections>().unwrap();
        assert_eq!(selections.0.len(), 1);
        assert!(selections.contains(4)); // index 4 is page 5
        assert!(!selections.contains(3));

        // Test comma-separated pages
        let selections = "1, 3, 5".parse::<PageSelections>().unwrap();
        assert_eq!(selections.0.len(), 3);
        assert!(selections.contains(0));
        assert!(!selections.contains(1));
        assert!(selections.contains(2));
        assert!(selections.contains(4));

        // Test range
        let selections = "1-5".parse::<PageSelections>().unwrap();
        assert_eq!(selections.0.len(), 1);
        assert!(selections.contains(0));
        assert!(selections.contains(2));
        assert!(selections.contains(4));
        assert!(!selections.contains(5));

        // Test mixed
        let selections = "1-2, 4, 6-7".parse::<PageSelections>().unwrap();
        assert_eq!(selections.0.len(), 3);
        assert!(selections.contains(0));
        assert!(selections.contains(1));
        assert!(!selections.contains(2));
        assert!(selections.contains(3));
        assert!(!selections.contains(4));
        assert!(selections.contains(5));
        assert!(selections.contains(6));
        assert!(!selections.contains(7));

        // Test with quotes and whitespace
        let selections = "\" 1-2, 4 \"".parse::<PageSelections>().unwrap();
        assert_eq!(selections.0.len(), 2);
        assert!(selections.contains(0));
        assert!(selections.contains(1));
        assert!(!selections.contains(2));
        assert!(selections.contains(3));
    }
}
