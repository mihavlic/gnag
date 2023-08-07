use std::error::Error;
use std::str::FromStr;

use lsp::error::ExtractError;
use lsp::msg::{Message, Request, RequestId, Response};
use lsp_types::OneOf;
use lsp_types::{
    request::GotoDefinition, GotoDefinitionResponse, InitializeParams, ServerCapabilities,
};

use lsp::connection::Connection;

fn main() -> Result<(), Box<dyn Error + Sync + Send>> {
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

    let server_capabilities = serde_json::to_value(&ServerCapabilities {
        definition_provider: Some(OneOf::Left(true)),
        ..Default::default()
    })
    .unwrap();

    let initialization_params = connection.initialize(server_capabilities).unwrap();
    main_loop(connection, initialization_params).unwrap();
    io_threads.join();

    Ok(())
}

fn main_loop(
    connection: Connection,
    params: serde_json::Value,
) -> Result<(), Box<dyn Error + Sync + Send>> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();
    for msg in connection.receive_iter() {
        match msg.unwrap() {
            Message::Request(req) if req.is_shutdown() => {
                connection.shutdown_and_exit(req.id)?;
                break;
            }
            Message::Request(req) => {
                match cast::<GotoDefinition>(req) {
                    Ok((id, params)) => {
                        let result = Some(GotoDefinitionResponse::Array(Vec::new()));
                        let result = serde_json::to_value(&result).unwrap();
                        let resp = Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        connection.send(Message::Response(resp))?;
                        continue;
                    }
                    Err(err @ ExtractError::JsonError { .. }) => panic!("{err:?}"),
                    Err(ExtractError::MethodMismatch) => {}
                };
                // ...
            }
            _ => {}
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
