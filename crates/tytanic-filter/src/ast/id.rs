use std::borrow::Borrow;
use std::fmt::Debug;
use std::ops::Deref;

use ecow::EcoString;
use pest::iterators::Pair;

use super::Error;
use super::PairExt;
use super::Rule;
use crate::eval;
use crate::eval::Context;
use crate::eval::Eval;
use crate::eval::Test;
use crate::eval::Value;

/// An identifier node.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Id(pub EcoString);

impl Id {
    /// The inner string.
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// Unwraps the inner EcoString.
    pub fn into_inner(self) -> EcoString {
        self.0
    }
}

impl Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Deref for Id {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl AsRef<str> for Id {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Borrow<str> for Id {
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl From<EcoString> for Id {
    fn from(value: EcoString) -> Self {
        Self(value)
    }
}

impl From<Id> for EcoString {
    fn from(value: Id) -> Self {
        value.into_inner()
    }
}

impl<T: Test> Eval<T> for Id {
    fn eval(&self, ctx: &Context<T>) -> Result<Value<T>, eval::Error> {
        ctx.resolve(self)
    }
}

impl Id {
    pub(super) fn parse(pair: Pair<'_, Rule>) -> Result<Id, Error> {
        pair.expect_rules(&[Rule::id])?;
        Ok(Id(pair.as_str().into()))
    }
}
