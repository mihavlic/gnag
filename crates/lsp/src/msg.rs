//! Code taken from rust-analyzer
//! https://github.com/rust-lang/rust-analyzer/blob/d398ad3326780598bbf1480014f4c59fbf6461a7/lib/lsp-server/src/msg.rs

use std::{
    fmt,
    io::{self, BufRead, Write},
};

use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::error::ExtractError;

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum Message {
    Request(Request),
    Response(Response),
    Notification(Notification),
}

impl From<Request> for Message {
    fn from(request: Request) -> Message {
        Message::Request(request)
    }
}

impl From<Response> for Message {
    fn from(response: Response) -> Message {
        Message::Response(response)
    }
}

impl From<Notification> for Message {
    fn from(notification: Notification) -> Message {
        Message::Notification(notification)
    }
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(transparent)]
pub struct RequestId(IdRepr);

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(untagged)]
enum IdRepr {
    I32(i32),
    String(String),
}

impl From<i32> for RequestId {
    fn from(id: i32) -> RequestId {
        RequestId(IdRepr::I32(id))
    }
}

impl From<String> for RequestId {
    fn from(id: String) -> RequestId {
        RequestId(IdRepr::String(id))
    }
}

impl fmt::Display for RequestId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            IdRepr::I32(it) => fmt::Display::fmt(it, f),
            // Use debug here, to make it clear that `92` and `"92"` are
            // different, and to reduce WTF factor if the sever uses `" "` as an
            // ID.
            IdRepr::String(it) => fmt::Debug::fmt(it, f),
        }
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Request {
    pub id: RequestId,
    pub method: String,
    #[serde(default = "serde_json::Value::default")]
    #[serde(skip_serializing_if = "serde_json::Value::is_null")]
    pub params: serde_json::Value,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Response {
    // JSON RPC allows this to be null if it was impossible
    // to decode the request's id. Ignore this special case
    // and just die horribly.
    pub id: RequestId,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub result: Option<serde_json::Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<ResponseError>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ResponseError {
    pub code: i32,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<serde_json::Value>,
}

#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum ErrorCode {
    // Defined by JSON RPC:
    ParseError = -32700,
    InvalidRequest = -32600,
    MethodNotFound = -32601,
    InvalidParams = -32602,
    InternalError = -32603,
    ServerErrorStart = -32099,
    ServerErrorEnd = -32000,

    /// Error code indicating that a server received a notification or
    /// request before the server has received the `initialize` request.
    ServerNotInitialized = -32002,
    UnknownErrorCode = -32001,

    // Defined by the protocol:
    /// The client has canceled a request and a server has detected
    /// the cancel.
    RequestCanceled = -32800,

    /// The server detected that the content of a document got
    /// modified outside normal conditions. A server should
    /// NOT send this error code if it detects a content change
    /// in it unprocessed messages. The result even computed
    /// on an older state might still be useful for the client.
    ///
    /// If a client decides that a result is not of any use anymore
    /// the client should cancel the request.
    ContentModified = -32801,

    /// The server cancelled the request. This error code should
    /// only be used for requests that explicitly support being
    /// server cancellable.
    ///
    /// @since 3.17.0
    ServerCancelled = -32802,

    /// A request failed but it was syntactically correct, e.g the
    /// method name was known and the parameters were valid. The error
    /// message should contain human readable information about why
    /// the request failed.
    ///
    /// @since 3.17.0
    RequestFailed = -32803,
}

impl From<ErrorCode> for i32 {
    fn from(value: ErrorCode) -> Self {
        value as i32
    }
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Notification {
    pub method: String,
    #[serde(default = "serde_json::Value::default")]
    #[serde(skip_serializing_if = "serde_json::Value::is_null")]
    pub params: serde_json::Value,
}

impl Message {
    /// Read precisely enough bytes from the `reader` to parse a [`Message`], returning [`io::ErrorKind::UnexpectedEof`] when the `reader` is exhausted while a message is being read.
    ///
    /// Do not rely on the contents of `scratch`.
    pub fn read(reader: &mut impl BufRead, scratch: &mut Vec<u8>) -> io::Result<Message> {
        Self::_read(reader, scratch)
    }
    pub fn _read(reader: &mut dyn BufRead, scratch: &mut Vec<u8>) -> io::Result<Message> {
        read_msg_text(reader, scratch)?;
        let msg = serde_json::from_slice(scratch)?;
        Ok(msg)
    }
    pub fn write(self, writer: &mut impl Write) -> io::Result<()> {
        self._write(writer)
    }
    pub fn _write(self, writer: &mut dyn Write) -> io::Result<()> {
        #[derive(Serialize)]
        struct JsonRpc {
            jsonrpc: &'static str,
            #[serde(flatten)]
            msg: Message,
        }
        let text = serde_json::to_string(&JsonRpc {
            jsonrpc: "2.0",
            msg: self,
        })?;
        write_msg_text(writer, &text)
    }
}

impl Response {
    pub fn new_ok<R: Serialize>(id: RequestId, result: R) -> Response {
        Response {
            id,
            result: Some(serde_json::to_value(result).unwrap()),
            error: None,
        }
    }
    pub fn new_err(id: RequestId, code: impl Into<i32>, message: String) -> Response {
        let error = ResponseError {
            code: code.into(),
            message,
            data: None,
        };
        Response {
            id,
            result: None,
            error: Some(error),
        }
    }
}

impl Request {
    pub fn new<P: Serialize>(id: RequestId, method: String, params: P) -> Request {
        Request {
            id,
            method,
            params: serde_json::to_value(params).unwrap(),
        }
    }
    pub fn extract<P: DeserializeOwned>(
        self,
        method: &str,
    ) -> Result<(RequestId, P), ExtractError> {
        if self.method != method {
            return Err(ExtractError::MethodMismatch);
        }
        let params = serde_json::from_value(self.params)?;
        Ok((self.id, params))
    }
    pub fn is_shutdown(&self) -> bool {
        self.method == "shutdown"
    }
    pub fn is_initialize(&self) -> bool {
        self.method == "initialize"
    }
}

impl Notification {
    pub fn new(method: impl Into<String>, params: impl Serialize) -> Notification {
        Notification {
            method: method.into(),
            params: serde_json::to_value(params).unwrap(),
        }
    }
    pub fn extract<P: DeserializeOwned>(self, method: &str) -> Result<P, ExtractError> {
        if self.method != method {
            return Err(ExtractError::MethodMismatch);
        }
        serde_json::from_value(self.params).map_err(Into::into)
    }
    pub(crate) fn is_exit(&self) -> bool {
        self.method == "exit"
    }
    pub(crate) fn is_initialized(&self) -> bool {
        self.method == "initialized"
    }
}

#[cold]
fn cold<T>(fun: impl FnOnce() -> T) -> T {
    fun()
}

/// Reads a json rpc message from `input`, the json part is left in the `buf`.
/// `buf` should be assumed to contain garbage if Result::Err is returned.
fn read_msg_text(reader: &mut dyn BufRead, buf: &mut Vec<u8>) -> io::Result<()> {
    // https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#headerPart
    //
    // Content-Length: ...\r\n
    // \r\n
    // {
    //     "jsonrpc": "2.0",
    //     "id": 1,
    //     "method": "textDocument/completion",
    //     "params": {
    //         ...
    //     }
    // }

    buf.clear();

    // read the header, extract Content-Length
    let mut size = None;
    loop {
        let cur = buf.len();
        reader.read_until(b'\n', buf)?;
        let just_read = &buf[cur..];

        let malformed_error = || {
            cold(|| {
                let err = if let Ok(str) = std::str::from_utf8(just_read) {
                    format!("malformed header: {str:?}")
                } else {
                    format!("malformed header: {just_read:?}")
                };

                Err(io::Error::new(io::ErrorKind::InvalidData, err))
            })
        };

        // the reader reached an EOF while reading the header
        // no actual message was read
        if just_read.len() == 0 {
            return cold(|| {
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "Eof while reading header",
                ))
            });
        }

        if !just_read.ends_with(b"\r\n") {
            return malformed_error();
        }

        // we've only read the `\r\n` delimiter, this occurs when we move past the header
        // and reach the `\r\n\r\n` which starts the json message
        if just_read.len() == 2 {
            break;
        }

        let line = &just_read[..just_read.len() - 2];

        // possibly use memchr for this
        let Some(split) = line.iter().position(|b| *b == b':') else {
            return malformed_error();
        };

        // name and value are separated by ': '
        if line[split + 1] != b' ' {
            return malformed_error();
        }

        let header_name = &line[..split];
        let header_value = &line[split + 2..];

        // it seems that all implementations only send the Content-Length header
        // we could add a special early path to check only for that
        match header_name {
            b"Content-Length" if header_value.iter().all(u8::is_ascii_digit) => {
                // SAFETY: we've just manually confirmed that all bytes in the array are an ascii subset
                let header_value = unsafe { std::str::from_utf8_unchecked(header_value) };
                let content_length = header_value
                    .parse::<usize>()
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

                size = Some(content_length);
            }
            b"Content-Type" => {
                assert_eq!(
                    header_value, b"application/vscode-jsonrpc; charset=utf-8",
                    "Other content-types are unsupported"
                );
            }
            _ => {
                return malformed_error();
            }
        }
    }

    let Some(size) = size else {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "No Content-Length"));
    };

    buf.resize(size, 0);
    reader.read_exact(buf)?;

    Ok(())
}

fn write_msg_text(out: &mut dyn Write, msg: &str) -> io::Result<()> {
    write!(out, "Content-Length: {}\r\n\r\n", msg.len())?;
    out.write_all(msg.as_bytes())?;
    out.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Message, Notification, Request, RequestId};

    #[test]
    fn shutdown_with_explicit_null() {
        let text = "{\"jsonrpc\": \"2.0\",\"id\": 3,\"method\": \"shutdown\", \"params\": null }";
        let msg: Message = serde_json::from_str(text).unwrap();

        assert!(
            matches!(msg, Message::Request(req) if req.id == 3.into() && req.method == "shutdown")
        );
    }

    #[test]
    fn shutdown_with_no_params() {
        let text = "{\"jsonrpc\": \"2.0\",\"id\": 3,\"method\": \"shutdown\"}";
        let msg: Message = serde_json::from_str(text).unwrap();

        assert!(
            matches!(msg, Message::Request(req) if req.id == 3.into() && req.method == "shutdown")
        );
    }

    #[test]
    fn notification_with_explicit_null() {
        let text = "{\"jsonrpc\": \"2.0\",\"method\": \"exit\", \"params\": null }";
        let msg: Message = serde_json::from_str(text).unwrap();

        assert!(matches!(msg, Message::Notification(not) if not.method == "exit"));
    }

    #[test]
    fn notification_with_no_params() {
        let text = "{\"jsonrpc\": \"2.0\",\"method\": \"exit\"}";
        let msg: Message = serde_json::from_str(text).unwrap();

        assert!(matches!(msg, Message::Notification(not) if not.method == "exit"));
    }

    #[test]
    fn serialize_request_with_null_params() {
        let msg = Message::Request(Request {
            id: RequestId::from(3),
            method: "shutdown".into(),
            params: serde_json::Value::Null,
        });
        let serialized = serde_json::to_string(&msg).unwrap();

        assert_eq!("{\"id\":3,\"method\":\"shutdown\"}", serialized);
    }

    #[test]
    fn serialize_notification_with_null_params() {
        let msg = Message::Notification(Notification {
            method: "exit".into(),
            params: serde_json::Value::Null,
        });
        let serialized = serde_json::to_string(&msg).unwrap();

        assert_eq!("{\"method\":\"exit\"}", serialized);
    }
}
