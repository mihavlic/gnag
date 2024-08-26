use std::{
    env::args,
    fmt::Display,
    path::{Path, PathBuf},
};

use gnag::{ast::ParsedFile, ctx::ErrorAccumulator};
use gnag_gen::{
    code::CodeFile,
    compile::CompiledFile,
    convert::ConvertedFile,
    graph::{debug_graphviz, debug_statements},
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

pub struct UnitPrinter {
    value: f64,
    suffixes: &'static [(&'static str, f64)],
}

#[allow(non_upper_case_globals)]
impl UnitPrinter {
    fn bytes(value: f64) -> Self {
        const KiB: f64 = 1.0 / 1024.0;
        const mB: f64 = 1024.0;

        Self {
            value,
            suffixes: &[
                ("MiB", KiB * KiB),
                ("KiB", KiB),
                ("B", 1.0),
                ("MiB", mB),
                ("MiB", mB * mB),
            ],
        }
    }
    fn seconds(value: f64) -> Self {
        const ms: f64 = 1000.0;
        Self {
            value,
            suffixes: &[
                ("s", 1.0),
                ("ms", ms),
                ("µs", ms * ms),
                ("ns", ms * ms * ms),
            ],
        }
    }
}

impl Display for UnitPrinter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut best: Option<(f64, &'static str)> = None;

        for &(name, factor) in self.suffixes {
            let value = self.value * factor;

            let mut new_best = true;
            if let Some((best, _)) = best {
                if best >= 1.0 {
                    new_best = value < best;
                } else {
                    new_best = value > best;
                }
            }

            if new_best {
                best = Some((value, name));
            }
        }

        let (value, suffix) = best.expect("No suffixes??");
        write!(f, "{value:.2} {suffix}")
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ErrorReporting {
    On,
    Eager,
    Off,
}

pub struct PhaseRunner<'a, 'b, 'c> {
    src: &'a str,
    file: &'b Path,
    err: &'c ErrorAccumulator,
    linemap: LineMap,
    errors: ErrorReporting,
    do_bench: bool,
    bytes: usize,
    iters: u32,
}

impl<'a, 'b, 'c> PhaseRunner<'a, 'b, 'c> {
    pub fn new(
        src: &'a str,
        file: &'b Path,
        err: &'c ErrorAccumulator,
        errors: ErrorReporting,
        do_bench: bool,
        iters: u32,
    ) -> PhaseRunner<'a, 'b, 'c> {
        assert!(iters > 0);
        PhaseRunner {
            src,
            err,
            file,
            linemap: LineMap::new(src),
            errors,
            do_bench,
            bytes: src.len(),
            iters,
        }
    }
    pub fn run<F: FnMut() -> T, T>(&self, name: &str, mut fun: F) -> T {
        let (elapsed, output) = {
            let start = std::time::Instant::now();
            let mut output = None;

            for _ in 0..self.iters {
                output = Some(fun());
            }

            let elapsed = (start.elapsed() / self.iters).as_secs_f64();

            (elapsed, output.unwrap())
        };

        let throughput = UnitPrinter::bytes((self.bytes as f64) / elapsed);
        let time = UnitPrinter::seconds(elapsed);

        if self.do_bench {
            eprintln!("{name}\t {time}\t {throughput}/s");
        }
        if self.errors == ErrorReporting::Eager {
            self.report_errors();
        }

        output
    }
    pub fn report_errors(&self) {
        if self.errors == ErrorReporting::Off {
            return;
        }

        let file = self.file.display();
        for e in self.err.get().iter() {
            let Utf16Pos { line, character } = self.linemap.offset_to_utf16(self.src, e.span.start);
            eprintln!("{file}:{}:{} {}", line + 1, character + 1, e.err);
        }
        self.err.clear();
    }
}

#[allow(unused_must_use)]
fn run() -> Result<(), ()> {
    let args = args().skip(1).collect::<Vec<_>>();

    let mut do_ast = false;
    let mut do_converted = false;
    let mut do_lowered = false;
    let mut do_dot = false;
    let mut do_statements = false;
    let mut do_scopes = false;
    let mut do_code = false;
    let mut do_file = false;

    let mut no_optimize = false;

    let mut do_bench = false;
    let mut bench_iters = 1;
    let mut file_repeat_count = 1;

    let mut errors = ErrorReporting::On;

    let mut files = Vec::new();
    let mut iter = args.iter().map(String::as_str);

    while let Some(arg) = iter.next() {
        match arg {
            "--ast" => do_ast = true,
            "--converted" => do_converted = true,
            "--lowered" => do_lowered = true,
            "--dot" => do_dot = true,
            "--statements" => do_statements = true,
            "--scopes" => do_scopes = true,
            "--code" => do_code = true,
            "--file" => do_file = true,
            "--no-optimize" => no_optimize = true,
            "--errors" => {
                let next = iter.next().expect("Expected argument");
                match next {
                    "eager" => errors = ErrorReporting::Eager,
                    "off" => errors = ErrorReporting::Off,
                    _ => panic!("Unexpected argument to --errors"),
                }
            }
            "--bench" => do_bench = true,
            "--iters" => {
                bench_iters = iter
                    .next()
                    .expect("Expected argument")
                    .parse::<u32>()
                    .expect("Expected number");
            }
            "--repeats" => {
                file_repeat_count = iter
                    .next()
                    .expect("Expected argument")
                    .parse::<u32>()
                    .expect("Expected number");
            }
            _ => files.push(arg),
        }
    }

    match files.len() {
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

    let path: PathBuf = files.pop().unwrap().into();
    let canonic = path
        .canonicalize()
        .pretty_error(&path, "Failed to canonicalize")?;

    let current_dir = std::env::current_dir().unwrap();
    let file = canonic.strip_prefix(current_dir).unwrap();

    let mut src = std::fs::read_to_string(&path).pretty_error(&path, "Failed to read")?;

    if file_repeat_count != 1 {
        src = src.repeat(file_repeat_count as usize);
    }

    let err = ErrorAccumulator::new();

    let runner = PhaseRunner::new(&src, file, &err, errors, do_bench, bench_iters);

    let parsed = runner.run("parse", || ParsedFile::new(&src, &err));
    let converted = runner.run("convert", || ConvertedFile::new(&src, &err, &parsed));
    let lowered = runner.run("lower", || LoweredFile::new(&src, &err, &converted));
    let compiled = runner.run("compile", || {
        CompiledFile::new(&err, &converted, &lowered, !no_optimize)
    });
    let code = runner.run("format", || CodeFile::new(&err, &converted, &compiled));

    runner.report_errors();

    if do_ast {
        let string = parsed.root.pretty_print_with_file(&src, &parsed);
        println!("{string}");
    }

    if do_converted {
        for (handle, rule) in converted.rules.iter_kv() {
            println!("\nrule {}:", handle.name(&converted),);
            rule.body
                .expr
                .display_with_indent(&mut StdoutSink, 1, &converted);
        }
        println!();
        for (handle, rule) in converted.inlines.iter_kv() {
            println!("\ninline {}:", handle.name(&converted),);
            rule.body
                .expr
                .display_with_indent(&mut StdoutSink, 1, &converted);
        }
    }

    if do_lowered {
        for (handle, rule) in lowered.rules.iter_kv() {
            println!("\nrule {}:", handle.name(&converted));
            rule.display_with_indent(&mut StdoutSink, 1, &converted);
        }
        println!();
    }

    if do_dot {
        let mut offset = 0;
        println!("digraph G {{");
        for (handle, graph) in compiled.rules.iter_kv() {
            debug_graphviz(
                &graph.nodes,
                &mut StdoutSink,
                handle.name(&converted),
                offset,
                &converted,
            );
            offset += graph.nodes.len();

            println!();
        }
        println!("}}\n");
    }

    if do_statements {
        for (handle, graph) in compiled.rules.iter_kv() {
            println!("rule {}", handle.name(&converted));
            debug_statements(&graph.nodes, &mut StdoutSink, &converted);
            println!();
        }
    }

    let structures = compiled
        .rules
        .map_ref(|graph| GraphStructuring::new(&graph.nodes));

    if do_scopes {
        for ((_, structuring), graph) in structures.iter_kv().zip(compiled.rules.iter()) {
            structuring.debug_scopes(&mut StdoutSink, &graph.nodes, &converted);

            println!();
        }
    }

    if do_code {
        for ((handle, structuring), graph) in structures.iter_kv().zip(compiled.rules.iter()) {
            print!("rule {} ", handle.name(&converted));

            let statements = structuring.emit_code(true, true, &graph.nodes);
            display_code(&mut StdoutSink, &statements, &graph.nodes, &converted);

            println!();
        }
    }

    if do_file {
        let source = file.display();
        let header = format!(
            "\
//! This file is generated by gnag-cli from '{source}'.
//! Edit the grammar file instead.

use gnag_runtime::lexer::*;
use gnag_runtime::parser::*;
use gnag_runtime::*;
"
        );

        let result = generate_code(&code);
        match result {
            Ok(ok) => {
                println!("{header}");
                println!("{ok}");
            }
            Err(e) => {
                eprintln!("Formatting failed, printing unformatted:");
                eprintln!("{e}");
            }
        }
    }

    Ok(())
}

fn generate_code(code: &CodeFile) -> Result<String, String> {
    let mut buffer = String::new();
    code.display(&mut buffer);
    let result = rustfmt_format(&buffer);
    result.map_err(|_| buffer)
}

// fn please_format(input: &str) -> syn::Result<String> {
//     let syntax_tree = syn::parse_file(input)?;
//     Ok(prettyplease::unparse(&syntax_tree))
// }

fn rustfmt_format(input: &str) -> std::io::Result<String> {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let mut child = Command::new("rustfmt")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("Failed to spawn child process");

    let mut stdin = child.stdin.take().expect("Failed to open stdin");

    std::thread::scope(move |s| {
        s.spawn(move || {
            stdin
                .write_all(input.as_bytes())
                .expect("Failed to write to stdin");
        });
    });

    let output = child.wait_with_output().expect("Failed to read stdout");

    let output = String::from_utf8(output.stdout).expect("Rustfmt returned non-utf8 data");
    Ok(output)
}
