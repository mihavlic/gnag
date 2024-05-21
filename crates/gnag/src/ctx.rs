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

#[derive(Default)]
pub struct ErrorAccumulator {
    errors: RefCell<Vec<SpannedError>>,
}

impl ErrorAccumulator {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn error(&self, span: StrSpan, err: impl ToString) {
        self.errors.borrow_mut().push(SpannedError {
            span,
            err: err.to_string(),
        });
    }
    pub fn get(&self) -> std::cell::Ref<Vec<SpannedError>> {
        self.errors.borrow()
    }
    pub fn clear(&self) {
        self.errors.borrow_mut().clear();
    }
}
