use std::{
    io::{self},
    panic::panic_any,
    sync::mpsc::{self},
    thread::{self, JoinHandle},
    time::Duration,
};

use crate::{
    error::ProtocolError,
    msg::{ErrorCode, Message, RequestId, Response},
};

pub struct Connection {
    pub receiver: mpsc::Receiver<io::Result<Message>>,
    pub sender: mpsc::Sender<Message>,
}

pub struct IoThreads {
    pub receiver: JoinHandle<()>,
    pub sender: JoinHandle<()>,
}

impl IoThreads {
    pub fn join(self) {
        _ = self.receiver.join();
        _ = self.sender.join();
    }
}

impl Connection {
    pub fn stdio() -> (Connection, IoThreads) {
        // the type of `io::stdin().lock()` is !Send so we can't use ['Self::custom()']
        Self::custom_loop(
            |tx| {
                let mut receiver = io::stdin().lock();
                receiver_loop(&mut receiver, tx)
            },
            |rx| {
                let mut sender = io::stdout().lock();
                sender_loop(&mut sender, rx)
            },
        )
    }
    pub fn custom(
        mut receiver: Box<dyn io::BufRead + Send>,
        mut sender: Box<dyn io::Write + Send>,
    ) -> (Connection, IoThreads) {
        Self::custom_loop(
            move |tx| receiver_loop(&mut receiver, tx),
            move |rx| sender_loop(&mut sender, rx),
        )
    }
    fn custom_loop(
        custom_receiver_loop: impl FnOnce(mpsc::Sender<io::Result<Message>>) + Send + 'static,
        custom_sender_loop: impl FnOnce(mpsc::Receiver<Message>) + Send + 'static,
    ) -> (Connection, IoThreads) {
        let (tx, receiver) = mpsc::channel();
        let receiver_join = thread::spawn(move || custom_receiver_loop(tx));

        let (sender, rx) = mpsc::channel();
        let sender_join = thread::spawn(move || custom_sender_loop(rx));

        let io = IoThreads {
            receiver: receiver_join,
            sender: sender_join,
        };

        let connection = Connection {
            receiver: receiver,
            sender: sender,
        };

        (connection, io)
    }
    pub fn initialize_start(&self) -> Result<(RequestId, serde_json::Value), ProtocolError> {
        loop {
            match self.receiver.recv()? {
                Ok(Message::Request(req)) if req.is_initialize() => {
                    return Ok((req.id, req.params));
                }
                // Respond to non-initialize requests with ServerNotInitialized
                Ok(Message::Request(req)) => {
                    let resp = Response::new_err(
                        req.id.clone(),
                        ErrorCode::ServerNotInitialized,
                        format!("expected initialize request, got {req:?}"),
                    );
                    self.send(resp)?;
                    continue;
                }
                Ok(Message::Notification(n)) if !n.is_exit() => {
                    continue;
                }
                Ok(msg) => {
                    return Err(ProtocolError(format!(
                        "expected initialize request, got {msg:?}"
                    )));
                }
                Err(e) => {
                    return Err(ProtocolError(format!(
                        "reader received malformed data, Err: {e:}"
                    )));
                }
            };
        }
    }
    pub fn initialize_finish(
        &self,
        initialize_id: RequestId,
        initialize_result: serde_json::Value,
    ) -> Result<(), ProtocolError> {
        let resp = Response::new_ok(initialize_id, initialize_result);
        self.send(resp)?;
        match self.receiver.recv()? {
            Ok(Message::Notification(n)) if n.is_initialized() => Ok(()),
            Ok(msg) => Err(ProtocolError(format!(
                r#"expected initialized notification, got: {msg:?}"#
            ))),
            Err(e) => Err(ProtocolError(format!(
                "expected initialized notification, got error: {e}",
            ))),
        }
    }
    pub fn initialize(
        &self,
        server_capabilities: serde_json::Value,
    ) -> Result<serde_json::Value, ProtocolError> {
        let (id, params) = self.initialize_start()?;

        let initialize_result = serde_json::json!({
            "capabilities": server_capabilities,
        });

        self.initialize_finish(id, initialize_result)?;

        Ok(params)
    }
    /// Acknowledges the Shutdown request and waits for Exit. You may want to handle shutdown differently.
    pub fn shutdown_and_exit(&self, id: RequestId) -> Result<(), ProtocolError> {
        let resp = Response::new_ok(id, ());
        self.send(resp)?;
        match &self.receiver.recv_timeout(Duration::from_secs(10))? {
            Ok(Message::Notification(n)) if n.is_exit() => (),
            Ok(msg) => {
                return Err(ProtocolError(format!(
                    "unexpected message during shutdown: {msg:?}"
                )))
            }
            Err(e) => {
                return Err(ProtocolError(format!(
                    "unexpected error during shutdown: {e}"
                )))
            }
        }
        Ok(())
    }
    pub fn send<T: Into<Message>>(&self, message: T) -> Result<(), mpsc::SendError<Message>> {
        self.sender.send(message.into())
    }
}

fn receiver_loop(receiver: &mut dyn io::BufRead, sender: mpsc::Sender<io::Result<Message>>) {
    let mut scratch = Vec::new();
    loop {
        match Message::_read(receiver, &mut scratch) {
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return,
            other => {
                if sender.send(other).is_err() {
                    return;
                }
            }
        }
    }
}

pub fn sender_loop(sender: &mut dyn io::Write, receiver: mpsc::Receiver<Message>) {
    while let Ok(message) = receiver.recv() {
        match message._write(sender) {
            Ok(()) => {}
            Err(e) => {
                if e.kind() == io::ErrorKind::UnexpectedEof {
                    return;
                } else {
                    panic_any(e);
                }
            }
        }
    }
}
