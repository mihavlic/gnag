use std::{
    env::args,
    path::{Path, PathBuf},
};

use gnag::{ast::ParsedFile, SpannedError};
use gnag_gen::{
    convert::ConvertedFile,
    graph::Graph,
    lower::LoweredFile,
    structure::{display_code, GraphStructuring},
};
use linemap::{LineMap, Utf16Pos};

trait IoError<T> {
    fn pretty_error(self, path: &Path, message: &str) -> Result<T, ()>;
}

impl<T> IoError<T> for std::io::Result<T> {
    fn pretty_error(self, path: &Path, message: &str) -> Result<T, ()> {
        self.map_err(|e| {
            let path = path.display();
            eprintln!("{message} `{path}`\n  {e}");
        })
    }
}

fn main() {
    if run().is_err() {
        std::process::exit(1);
    }
}

struct StdoutSink;

impl std::fmt::Write for StdoutSink {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        use std::io::Write as _;
        std::io::stdout()
            .write_all(s.as_bytes())
            .map_err(|_| std::fmt::Error)
    }
}

#[allow(unused_must_use)]
fn run() -> Result<(), ()> {
    let mut args = args().skip(1).collect::<Vec<_>>();

    let mut do_ast = false;
    let mut do_converted = false;
    let mut do_lowered = false;
    let mut do_dot = false;
    let mut do_statements = false;
    let mut do_scopes = false;
    let mut do_code = false;

    let mut none_enabled = true;
    args.retain(|arg| {
        match arg.as_str() {
            "--ast" => do_ast = true,
            "--converted" => do_converted = true,
            "--lowered" => do_lowered = true,
            "--dot" => do_dot = true,
            "--statements" => do_statements = true,
            "--scopes" => do_scopes = true,
            "--code" => do_code = true,
            _ => return true,
        }
        none_enabled = false;
        false
    });

    match args.len() {
        0 => {
            eprintln!("No file provided");
            return Err(());
        }
        1 => {}
        _ => {
            eprintln!("Only one file may be provided");
            return Err(());
        }
    }

    let path: PathBuf = args.pop().unwrap().into();
    let canonic = path
        .canonicalize()
        .pretty_error(&path, "Failed to canonicalize")?;

    let current_dir = std::env::current_dir().unwrap();
    let file = canonic.strip_prefix(current_dir).unwrap();

    let src = std::fs::read_to_string(&path).pretty_error(&path, "Failed to read")?;

    let linemap = LineMap::new(&src);
    let report = |errors: &[SpannedError]| {
        let file = file.display();
        for e in errors {
            let Utf16Pos { line, character } = linemap.offset_to_utf16(&src, e.span.start);
            eprintln!("{file}:{}:{} {}", line + 1, character + 1, e.err);
        }
    };

    let parsed = ParsedFile::new(&src);
    report(&parsed.errors);
    let converted = ConvertedFile::new(&src, &parsed);
    report(&converted.errors);
    let lowered = LoweredFile::new(&src, &converted);
    report(&lowered.errors);

    if do_ast || none_enabled {
        let string = parsed.root.pretty_print_with_file(&src, &parsed);
        println!("{string}");
    }

    if do_converted || none_enabled {
        for (handle, token) in converted.tokens.iter_kv() {
            println!("token {}: {:#?}", handle.name(&converted), token.pattern);
        }
        for (handle, rule) in converted.rules.iter_kv() {
            println!("\nrule {}:", handle.name(&converted),);
            rule.expr
                .display_with_indent(&mut StdoutSink, 1, &converted);
        }
        println!();
    }

    if do_lowered || none_enabled {
        for (handle, token) in lowered.tokens.iter_kv() {
            println!("token {}: {token}", handle.name(&converted));
        }
        for (handle, rule) in lowered.rules.iter_kv() {
            println!("\nrule {}:", handle.name(&converted));
            rule.display_with_indent(&mut StdoutSink, 1, &converted);
        }
        println!();
    }

    let graphs = lowered
        .rules
        .map_ref_with_key(|handle, expr| Graph::new(handle, expr));

    if do_dot || none_enabled {
        let mut offset = 0;
        println!("digraph G {{");
        for (handle, graph) in graphs.iter_kv() {
            graph.debug_graphviz(&mut StdoutSink, handle.name(&converted), offset, &converted);
            offset += graph.get_nodes().len();

            println!();
        }
        println!("}}\n");
    }

    if do_statements || none_enabled {
        for (handle, graph) in graphs.iter_kv() {
            println!("rule {}", handle.name(&converted));
            graph.debug_statements(&mut StdoutSink, &converted);

            println!();
        }
    }

    let structures = graphs.map_ref(GraphStructuring::new);

    if do_scopes || none_enabled {
        for ((_, structuring), graph) in structures.iter_kv().zip(graphs.iter()) {
            structuring.debug_scopes(&mut StdoutSink, &graph, &converted);

            println!();
        }
    }

    if do_code || none_enabled {
        for ((handle, structuring), graph) in structures.iter_kv().zip(graphs.iter()) {
            print!("rule {} ", handle.name(&converted));
            let statements = structuring.emit_code(true, true, graph);
            display_code(&mut StdoutSink, &statements, graph, &converted);

            println!();
        }
    }

    Ok(())
}
