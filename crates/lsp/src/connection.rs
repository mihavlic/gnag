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
    receiver: mpsc::Receiver<io::Result<Message>>,
    sender: mpsc::Sender<Message>,
    receive_handler: Option<fn(&io::Result<Message>)>,
    send_handler: Option<fn(&Message)>,
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
    pub fn new(
        receiver: mpsc::Receiver<io::Result<Message>>,
        sender: mpsc::Sender<Message>,
    ) -> Connection {
        Self {
            receiver,
            sender,
            receive_handler: None,
            send_handler: None,
        }
    }
    pub fn set_receive_inspect(&mut self, fun: fn(&io::Result<Message>)) {
        self.receive_handler = Some(fun);
    }
    pub fn set_send_inspect(&mut self, fun: fn(&Message)) {
        self.send_handler = Some(fun);
    }
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

        let connection = Connection::new(receiver, sender);

        (connection, io)
    }
    // read the spec
    // <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#initialize>
    pub fn initialize_start(
        &self,
    ) -> Result<(RequestId, lsp_types::InitializeParams), ProtocolError> {
        loop {
            match self.receive()? {
                Ok(Message::Request(req)) if req.is_initialize() => {
                    let params = serde_json::from_value(req.params)
                        .map_err(|e| ProtocolError(e.to_string()))?;
                    return Ok((req.id, params));
                }
                // Respond to non-initialize requests with ServerNotInitialized
                Ok(Message::Request(req)) => {
                    let resp = Response::new_err(
                        req.id.clone(),
                        ErrorCode::ServerNotInitialized,
                        format!("expected initialize request, got {req:?}"),
                    );
                    self.send(resp)?;
                }
                Ok(Message::Notification(n)) if !n.is_exit() => {}
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
        initialize_response: &lsp_types::InitializeResult,
    ) -> Result<(), ProtocolError> {
        let resp = Response::new_ok(initialize_id, initialize_response);
        self.send(resp)?;

        match self.receive()? {
            Ok(Message::Notification(n)) if n.is_initialized() => Ok(()),
            Ok(msg) => Err(ProtocolError(format!(
                r#"expected initialized notification, got: {msg:?}"#
            ))),
            Err(e) => Err(ProtocolError(format!(
                "expected initialized notification, got error: {e}",
            ))),
        }
    }
    /// Acknowledges the Shutdown request and waits for Exit. You may want to handle shutdown differently.
    pub fn shutdown_and_exit(&self, id: RequestId) -> Result<(), ProtocolError> {
        let resp = Response::new_ok(id, ());
        self.send(resp)?;
        match &self.receive_timeout(Duration::from_secs(10))? {
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
        let message = message.into();
        if let Some(fun) = self.send_handler {
            fun(&message);
        }
        self.sender.send(message)
    }

    pub fn receive(&self) -> Result<io::Result<Message>, mpsc::RecvError> {
        let res = self.receiver.recv();
        if let Some(fun) = self.receive_handler {
            if let Ok(message) = &res {
                fun(message);
            }
        }
        res
    }
    pub fn receive_timeout(
        &self,
        timeout: Duration,
    ) -> Result<io::Result<Message>, mpsc::RecvTimeoutError> {
        let res = self.receiver.recv_timeout(timeout);
        if let Some(fun) = self.receive_handler {
            if let Ok(message) = &res {
                fun(message);
            }
        }
        res
    }
    pub fn try_receive(&self) -> Result<io::Result<Message>, mpsc::TryRecvError> {
        let res = self.receiver.try_recv();
        if let Some(fun) = self.receive_handler {
            if let Ok(message) = &res {
                fun(message);
            }
        }
        res
    }
    pub fn receive_iter(&self) -> ReceiveIter<'_> {
        ReceiveIter(self)
    }
}

pub struct ReceiveIter<'a>(&'a Connection);
impl<'a> Iterator for ReceiveIter<'a> {
    type Item = io::Result<Message>;
    fn next(&mut self) -> Option<Self::Item> {
        // the iterator contract is preserved, once recv() returns None, it can never send anything else
        self.0.receive().ok()
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
    let mut scratch = Vec::new();
    while let Ok(message) = receiver.recv() {
        match message._write(sender, &mut scratch) {
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
