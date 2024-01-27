use std::{borrow::Borrow, cell::RefCell};

use crate::{SpannedError, StrSpan};

pub trait SpanExt {
    fn resolve<'a, S: Borrow<str> + 'a>(self, cx: &'a S) -> &'a str;
    fn resolve_owned<S: Borrow<str>>(self, cx: &S) -> String;
}

impl SpanExt for StrSpan {
    fn resolve<'a, S: Borrow<str> + 'a>(self, cx: &'a S) -> &'a str {
        self.as_str(cx.borrow())
    }

    fn resolve_owned<S: Borrow<str>>(self, cx: &S) -> String {
        self.as_str(cx.borrow()).to_owned()
    }
}

pub struct ConvertCtx<'a> {
    src: &'a str,
    errors: RefCell<Vec<SpannedError>>,
}

impl<'a> ConvertCtx<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            errors: Default::default(),
        }
    }
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.errors.borrow_mut().push(SpannedError {
            span,
            err: err.to_string(),
        });
    }
    pub fn finish(self) -> Vec<SpannedError> {
        RefCell::into_inner(self.errors)
    }
}

impl Borrow<str> for ConvertCtx<'_> {
    fn borrow(&self) -> &str {
        self.src
    }
}
