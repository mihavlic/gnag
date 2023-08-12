mod ctx;
mod executor;
mod ext;
mod linemap;
mod tokens;

use std::str::FromStr;
use std::sync::mpsc;

use anyhow::Context;
use ctx::{Config, Ctx};
use lsp::error::ExtractError;
use lsp::msg::{ErrorCode, Message, Request, RequestId, Response};
use lsp_types::*;

use lsp::connection::Connection;
use tokens::{TokenModifier, TokenType};

fn main() {
    let level = std::env::var("RUST_LOG").unwrap_or_else(|_| "TRACE".to_owned());
    let level = log::LevelFilter::from_str(&level).unwrap();

    simplelog::TermLogger::init(
        level,
        simplelog::ConfigBuilder::new()
            .set_time_format_custom(&[])
            .build(),
        simplelog::TerminalMode::Stderr,
        simplelog::ColorChoice::Never,
    )
    .unwrap();

    // <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#initialize>
    // The server is not allowed to send any requests or notifications to the client until it has
    // responded with an InitializeResult, with the exception that during the initialize request
    // the server is allowed to send the notifications `window/showMessage`, `window/logMessage` and
    // `telemetry/event` as well as the `window/showMessageRequest` request to the client

    let (mut connection, io_threads) = Connection::stdio();
    if level == log::Level::Trace {
        connection.set_receive_inspect(|result| match result {
            Ok(msg) => {
                let json = serde_json::to_string_pretty(msg).unwrap();
                log::trace!("\n> {json}")
            }
            Err(err) => log::error!("> {err}"),
        });
        connection.set_send_inspect(|msg| {
            let json = serde_json::to_string_pretty(msg).unwrap();
            log::trace!("\n< {json}")
        });
    }

    let config = init(&connection).unwrap();
    let cx = Ctx::new(config);

    main_loop(connection, cx).unwrap();
    io_threads.join();
}

fn init(connection: &Connection) -> anyhow::Result<Config> {
    let (id, params) = connection.initialize_start()?;

    let config = Config::new(params.initialization_options.unwrap())?;

    let semantic_tokens_provider = config.semantic_tokens.then(|| SemanticTokensOptions {
        legend: SemanticTokensLegend {
            token_types: TokenType::types().to_vec(),
            token_modifiers: TokenModifier::types().to_vec(),
        },
        full: Some(SemanticTokensFullOptions::Delta { delta: Some(true) }),
        ..Default::default()
    });

    if semantic_tokens_provider.is_some() {
        log::warn!("TODO semantic tokens");
    }

    let capabilities = ServerCapabilities {
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec![]),
            ..Default::default()
        }),
        text_document_sync: Some(TextDocumentSyncCapability::Options(
            TextDocumentSyncOptions {
                open_close: Some(true),
                change: Some(TextDocumentSyncKind::INCREMENTAL),
                save: Some(TextDocumentSyncSaveOptions::Supported(true)),
                ..Default::default()
            },
        )),
        document_symbol_provider: Some(OneOf::Left(true)),
        definition_provider: Some(OneOf::Left(true)),
        document_formatting_provider: Some(OneOf::Left(true)),
        diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
            identifier: None,
            inter_file_dependencies: false,
            workspace_diagnostics: false,
            work_done_progress_options: WorkDoneProgressOptions {
                work_done_progress: None,
            },
        })),
        ..Default::default()
    };

    let response = InitializeResult {
        capabilities,
        server_info: Some(ServerInfo {
            name: "gnag-lsp".to_owned(),
            version: Some(env!("CARGO_PKG_VERSION").to_owned()),
        }),
    };

    connection.initialize_finish(id, &response)?;

    Ok(config)
}

fn main_loop(connection: Connection, mut cx: Ctx) -> anyhow::Result<()> {
    for msg in connection.receive_iter() {
        match msg.context("Stdin reader failed")? {
            Message::Request(req) => {
                let Request { id, method, params } = req;

                let error = |code: ErrorCode, message: String| {
                    connection.send(Response::new_err(id.clone(), code, message))
                };

                let response =
                    |response: &dyn JsonSerialize| -> Result<(), mpsc::SendError<Message>> {
                        connection.send(Message::Response(Response {
                            id: id.clone(),
                            result: Some(response.json_serialize().unwrap()),
                            error: None,
                        }))
                    };

                match &*method {
                    _ if method.starts_with("$") => {
                        // <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#dollarRequests>
                        //   If a server or client receives a request starting with ‘$/’ it must
                        //   error the request with error code MethodNotFound
                        error(
                            ErrorCode::MethodNotFound,
                            "Request methods starting with '$' are automatically errored.".into(),
                        )?;
                    }
                    "shutdown" => {
                        connection.shutdown_and_exit(id)?;
                        break;
                    }
                    "textDocument/definition" => {
                        response(&GotoDefinitionResponse::Array(Vec::new()))?;
                    }
                    _ => {
                        error(
                            ErrorCode::RequestFailed,
                            format!("Unsupported request '{}'", method),
                        )?;
                    }
                }
            }
            Message::Notification(not) => {
                let lsp::msg::Notification { method, params } = not;

                use lsp_types::notification::*;
                match &*method {
                    "textDocument/didOpen" => {
                        let params = params.to::<DidOpenTextDocument>()?;
                        // cx.file = params.
                    }
                    "textDocument/didChange" => {}
                    _ => {}
                }
            }
            Message::Response(_) => unreachable!("A server can't get a Response?"),
        }
    }
    Ok(())
}

fn cast<R>(req: Request) -> Result<(RequestId, R::Params), ExtractError>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    req.extract(R::METHOD)
}

trait NotificationExtract {
    fn to<N: lsp_types::notification::Notification>(self) -> serde_json::Result<N::Params>;
}

impl NotificationExtract for serde_json::Value {
    fn to<N: lsp_types::notification::Notification>(self) -> serde_json::Result<N::Params> {
        serde_json::from_value(self)
    }
}

trait JsonSerialize {
    fn json_serialize(&self) -> Result<serde_json::Value, serde_json::Error>;
}

impl<T: serde::Serialize> JsonSerialize for T {
    fn json_serialize(&self) -> Result<serde_json::Value, serde_json::Error> {
        serde_json::to_value(self)
    }
}
