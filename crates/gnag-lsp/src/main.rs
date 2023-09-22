mod ctx;
mod ext;
mod handlers;
mod lsp_ext;

use std::{fmt::Display, str::FromStr};

use anyhow::Context;
use ctx::{Config, Ctx};
use lsp::msg::{ErrorCode, Message, Request, Response, ResponseError};
use lsp_types::*;

use lsp::connection::Connection;

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
    let mut cx = Ctx::new(config, connection);

    main_loop(&mut cx).unwrap();

    io_threads.join();
}

fn init(connection: &Connection) -> anyhow::Result<Config> {
    let (id, params) = connection.initialize_start()?;

    let config = Config::new(params.initialization_options.unwrap())?;

    let capabilities = ServerCapabilities {
        completion_provider: Some(CompletionOptions::default()),
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
        // document_formatting_provider: Some(OneOf::Left(true)),
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

struct PositionDisplay<'a>(&'a lsp_types::TextDocumentPositionParams);
impl Display for PositionDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let TextDocumentPositionParams {
            text_document,
            position,
        } = self.0;
        write!(
            f,
            "{}:{}:{}",
            text_document.uri.as_str(),
            position.line + 1,
            position.character + 1
        )
    }
}

fn main_loop(cx: &mut Ctx) -> anyhow::Result<()> {
    while let Ok(msg) = cx.receive() {
        match msg.context("Stdin reader failed")? {
            Message::Request(req) => {
                let Request { id, method, params } = req;

                let result = match method.as_str() {
                    _ if method.starts_with("$") => {
                        // <https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#dollarRequests>
                        // If a server or client receives a request starting with $,
                        // it must error the request with error code MethodNotFound
                        cx.error(
                            id,
                            ErrorCode::MethodNotFound,
                            "Request methods starting with '$' are automatically errored.",
                        )?;
                        continue;
                    }
                    "shutdown" => {
                        cx.shutdown_and_exit(id)?;
                        break;
                    }
                    "textDocument/definition" => {
                        let params: GotoDefinitionParams = serde_json::from_value(params)?;
                        log::trace!(
                            "textDocument/completion {}",
                            PositionDisplay(&params.text_document_position_params)
                        );
                        handlers::definition(cx, &params)
                    }
                    "textDocument/documentSymbol" => {
                        handlers::document_symbol(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/completion" => {
                        let params: CompletionParams = serde_json::from_value(params)?;
                        log::trace!(
                            "textDocument/completion {}",
                            PositionDisplay(&params.text_document_position)
                        );
                        handlers::completion(cx, &params)
                    }
                    "textDocument/formatting" => {
                        handlers::formatting(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/diagnostic" => {
                        handlers::diagnostic(cx, &serde_json::from_value(params)?)
                    }
                    "gnag-lsp/showAst" => handlers::show_ast(cx, &serde_json::from_value(params)?),
                    "gnag-lsp/showIr" => handlers::show_ir(cx, &serde_json::from_value(params)?),
                    "gnag-lsp/showLoweredIr" => {
                        handlers::show_lowered_ir(cx, &serde_json::from_value(params)?)
                    }
                    _ => {
                        cx.error(
                            id,
                            ErrorCode::RequestFailed,
                            format!("Unsupported request '{}'", method),
                        )?;
                        continue;
                    }
                };

                let response = match result {
                    Ok(ok) => Message::Response(Response {
                        id,
                        result: Some(ok),
                        error: None,
                    }),
                    Err(e) => Message::Response(Response {
                        id: id,
                        result: None,
                        error: Some(ResponseError {
                            code: ErrorCode::InternalError.into(),
                            message: e.to_string(),
                            data: None,
                        }),
                    }),
                };
                cx.send(response)?;
            }
            Message::Notification(not) => {
                let lsp::msg::Notification { method, params } = not;

                match &*method {
                    "textDocument/didOpen" => {
                        let params: DidOpenTextDocumentParams = serde_json::from_value(params)?;
                        let document = params.text_document;
                        cx.file_opened(document.uri.into(), document.text, document.version);
                    }
                    "textDocument/didClose" => {
                        let params: DidCloseTextDocumentParams = serde_json::from_value(params)?;
                        let document = params.text_document;
                        cx.file_closed(document.uri.as_ref());
                    }
                    "textDocument/didChange" => {
                        let params: DidChangeTextDocumentParams = serde_json::from_value(params)?;
                        let document = params.text_document;
                        cx.modify_file(
                            document.uri.as_ref(),
                            document.version,
                            &params.content_changes,
                        )?;
                    }
                    _ => {}
                }
            }
            Message::Response(_) => unreachable!("A server can't get a Response?"),
        }
    }
    Ok(())
}
