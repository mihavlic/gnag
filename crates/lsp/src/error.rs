//! Code taken from rust-analyzer
//! https://github.com/rust-lang/rust-analyzer/blob/d398ad3326780598bbf1480014f4c59fbf6461a7/lib/lsp-server/src/error.rs

use std::{error, fmt, sync::mpsc};

#[derive(Debug, Clone, PartialEq)]
pub struct ProtocolError(pub(crate) String);

impl error::Error for ProtocolError {}
impl fmt::Display for ProtocolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}
impl<T> From<mpsc::SendError<T>> for ProtocolError {
    fn from(_: mpsc::SendError<T>) -> Self {
        ProtocolError("Sender thread died".into())
    }
}
impl From<mpsc::RecvError> for ProtocolError {
    fn from(_: mpsc::RecvError) -> Self {
        ProtocolError("Receiver thread died".into())
    }
}
impl From<mpsc::RecvTimeoutError> for ProtocolError {
    fn from(_: mpsc::RecvTimeoutError) -> Self {
        ProtocolError("Timed out waiting for receiver".into())
    }
}

#[derive(Debug)]
pub enum ExtractError {
    /// The extracted message was of a different method than expected.
    MethodMismatch,
    /// Failed to deserialize the message.
    JsonError(serde_json::Error),
}

impl error::Error for ExtractError {}
impl fmt::Display for ExtractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExtractError::MethodMismatch => {
                write!(f, "Method mismatch")
            }
            ExtractError::JsonError(e) => {
                write!(f, "Invalid request\n{e}",)
            }
        }
    }
}
impl From<serde_json::Error> for ExtractError {
    fn from(value: serde_json::Error) -> Self {
        ExtractError::JsonError(value)
    }
}
