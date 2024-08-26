use std::{borrow::Cow, cell::RefCell};

use crate::span::{Span, Spanned};

pub type Error = Cow<'static, str>;

#[derive(Default)]
pub struct ErrorAccumulator {
    errors: RefCell<Vec<Spanned<Error>>>,
}

impl ErrorAccumulator {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn error_static(&self, span: Span, err: &'static str) {
        self.errors
            .borrow_mut()
            .push(Spanned::new(err.into(), span));
    }
    pub fn error(&self, span: Span, err: impl ToString) {
        self.errors
            .borrow_mut()
            .push(Spanned::new(err.to_string().into(), span));
    }
    pub fn get(&self) -> std::cell::Ref<Vec<Spanned<Error>>> {
        self.errors.borrow()
    }
    pub fn clear(&self) {
        self.errors.borrow_mut().clear();
    }
}
