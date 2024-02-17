use std::{env::args, fmt::Write, path::PathBuf};

use gnag::{ast::ParsedFile, SpannedError};
use gnag_gen::{
    convert::ConvertedFile,
    graph::Graph,
    lower::LoweredFile,
    structure::{display_code, GraphStructuring},
};
use linemap::{LineMap, Utf16Pos};

#[allow(unused_must_use)]
fn main() {
    let mut args = args().skip(1).collect::<Vec<_>>();

    let mut do_dot = false;
    let mut do_statements = false;
    let mut do_scopes = false;
    let mut do_code = false;

    args.retain(|arg| {
        match arg.as_str() {
            "--dot" => do_dot = true,
            "--statements" => do_statements = true,
            "--scopes" => do_scopes = true,
            "--code" => do_code = true,
            _ => return true,
        }
        false
    });

    if !(do_dot || do_statements || do_scopes || do_code) {
        do_dot = true;
        do_statements = true;
        do_scopes = true;
        do_code = true;
    }

    match args.len() {
        0 => {
            eprintln!("No file provided");
            std::process::exit(1);
        }
        1 => {}
        _ => {
            eprintln!("Only one file may be provided");
            std::process::exit(1);
        }
    }

    let path: PathBuf = args.pop().unwrap().into();
    let canonic = path.canonicalize().unwrap();

    let current_dir = std::env::current_dir().unwrap();
    let file = canonic.strip_prefix(current_dir).unwrap();

    let src = match std::fs::read_to_string(&path) {
        Ok(ok) => ok,
        Err(e) => {
            eprintln!("Failed to read `{}`\n  {e}", path.display());
            std::process::exit(1);
        }
    };

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

    if do_dot {
        let mut offset = 0;
        writeln!(buf, "digraph G {{");
        for (name, graph, _) in &finalish {
            graph.debug_graphviz(&mut buf, name, offset, &converted);
            offset += graph.get_nodes().len();

            writeln!(buf);
        }
        writeln!(buf, "}}\n");
    }

    if do_statements {
        for (name, graph, _) in &finalish {
            writeln!(buf, "rule {name}");
            graph.debug_statements(&mut buf, &converted);

            writeln!(buf);
        }
    }

    if do_scopes {
        for (_, graph, structure) in &finalish {
            structure.debug_scopes(&mut buf, &graph, &converted);

            writeln!(buf);
        }
    }

    if do_code {
        for (name, graph, structure) in &finalish {
            write!(buf, "rule {name} ");
            let statements = structure.emit_code(true, &graph);
            display_code(&mut buf, &statements, &graph, &converted);

            writeln!(buf);
        }
    }

    print!("{buf}");
}
