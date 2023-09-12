mod ctx;
mod executor;
mod ext;
mod handlers;
mod linemap;
mod tokens;

use std::str::FromStr;
use std::sync::mpsc;

use anyhow::Context;
use ctx::{Config, Ctx};
use lsp::error::ExtractError;
use lsp::msg::{ErrorCode, Message, Request, RequestId, Response, ResponseError};
use lsp_types::*;

use lsp::connection::Connection;
use lsp_types::request::GotoDefinition;
use serde::de::DeserializeOwned;
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
    let mut cx = Ctx::new(config, connection);

    main_loop(&mut cx).unwrap();

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
        // completion_provider: Some(CompletionOptions {
        //     trigger_characters: Some(vec![]),
        //     ..Default::default()
        // }),
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
                        handlers::definition(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/documentSymbol" => {
                        handlers::document_symbol(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/completion" => {
                        handlers::completion(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/formatting" => {
                        handlers::formatting(cx, &serde_json::from_value(params)?)
                    }
                    "textDocument/diagnostic" => {
                        handlers::diagnostic(cx, &serde_json::from_value(params)?)
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
