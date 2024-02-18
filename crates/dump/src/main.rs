use std::{
    env::args,
    fmt::Write,
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

#[allow(unused_must_use)]
fn run() -> Result<(), ()> {
    let mut args = args().skip(1).collect::<Vec<_>>();

    let mut do_converted = false;
    let mut do_lowered = false;
    let mut do_dot = false;
    let mut do_statements = false;
    let mut do_scopes = false;
    let mut do_code = false;

    let mut none_enabled = true;
    args.retain(|arg| {
        match arg.as_str() {
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

    let finalish = lowered
        .rules
        .iter_kv()
        .map(|(handle, expr)| {
            let name = converted.rules[handle].name.as_str();
            let graph = Graph::new(handle, expr);
            let structure = GraphStructuring::new(&graph);
            (name, graph, structure)
        })
        .collect::<Vec<_>>();

    let mut buf = String::new();

    if do_converted || none_enabled {
        for (handle, token) in converted.tokens.iter_kv() {
            writeln!(
                buf,
                "token {}: {:#?}",
                handle.name(&converted),
                token.pattern
            );
        }
        for (handle, rule) in converted.rules.iter_kv() {
            writeln!(buf, "\nrule {}:", handle.name(&converted),);
            rule.expr.display_with_indent(&mut buf, 1, &converted);
        }
        writeln!(buf);
    }

    if do_lowered || none_enabled {
        for (handle, token) in lowered.tokens.iter_kv() {
            writeln!(buf, "token {}: {token}", handle.name(&converted));
        }
        for (handle, rule) in lowered.rules.iter_kv() {
            writeln!(buf, "\nrule {}:", handle.name(&converted));
            rule.display_with_indent(&mut buf, 1, &converted);
        }
        writeln!(buf);
    }

    if do_dot || none_enabled {
        let mut offset = 0;
        writeln!(buf, "digraph G {{");
        for (name, graph, _) in &finalish {
            graph.debug_graphviz(&mut buf, name, offset, &converted);
            offset += graph.get_nodes().len();

            writeln!(buf);
        }
        writeln!(buf, "}}\n");
    }

    if do_statements || none_enabled {
        for (name, graph, _) in &finalish {
            writeln!(buf, "rule {name}");
            graph.debug_statements(&mut buf, &converted);

            writeln!(buf);
        }
    }

    if do_scopes || none_enabled {
        for (_, graph, structure) in &finalish {
            structure.debug_scopes(&mut buf, &graph, &converted);

            writeln!(buf);
        }
    }

    if do_code || none_enabled {
        for (name, graph, structure) in &finalish {
            write!(buf, "rule {name} ");
            let statements = structure.emit_code(true, &graph);
            display_code(&mut buf, &statements, &graph, &converted);

            writeln!(buf);
        }
    }

    print!("{buf}");
    Ok(())
}
