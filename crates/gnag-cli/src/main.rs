#![allow(dead_code)]

use std::{
    env::args,
    fmt::{Display, Write},
    ops::Deref,
    path::{Path, PathBuf},
};

use code_render::RenderCx;
use gnag_backend::{
    ast::Ast, backend::grammar::Grammar, codegen::render_file, error::ErrorAccumulator,
};
use gnag_parser::LANGUAGE;
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
            let Utf16Pos { line, character } =
                self.linemap.offset_to_utf16(self.src, e.span.start());
            eprintln!("{file}:{}:{} {}", line + 1, character + 1, e.deref());
        }
        self.err.clear();
    }
}

#[allow(unused_must_use)]
fn run() -> Result<(), ()> {
    let args = args().skip(1).collect::<Vec<_>>();

    let mut do_parse = false;
    let mut do_ast = false;
    let mut do_lower = false;
    let mut do_grammar = false;
    let mut do_code = false;

    let mut do_bench = false;
    let mut bench_iters = 1;
    let mut file_repeat_count = 1;

    let mut errors = ErrorReporting::On;

    let mut files = Vec::new();
    let mut iter = args.iter().map(String::as_str);

    while let Some(arg) = iter.next() {
        match arg {
            "--parse" => do_parse = true,
            "--ast" => do_ast = true,
            "--lower" => do_lower = true,
            "--grammar" => do_grammar = true,
            "--code" => do_code = true,
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
            _ if arg.starts_with("--") => {
                eprintln!("Unknown arg {arg:?}");
                return Err(());
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

    let tokens = LANGUAGE.lex_all(src.as_bytes());
    let trace = LANGUAGE.parse_all(&tokens);
    let trace = trace.to_preorder(&mut Vec::new());

    if do_parse {
        println!();
        print!("{}", trace.display(&LANGUAGE, false));
    }

    let ast = Ast::new(&src, &trace, &err);

    let mut grammar = Grammar::new(&ast, &err);

    if grammar.rules.iter().count() == 0 {
        println!("Parsing produced no rules");
    }

    if !do_ast || do_lower || do_code {
        grammar.resolve(&err);
        grammar.lower(&err);
        grammar.create_lexer(&err);
        grammar.create_pratt_rules(&err);
        grammar.finish_rules();
    }

    let mut buf = String::new();

    if do_ast || do_grammar || (!do_parse && !do_code) || do_lower {
        for (_, rule) in grammar.rules.iter() {
            _ = write!(buf, "\n{} =\n", rule.name);
            rule.pattern.display_into_indent(&mut buf, &grammar, 1);
        }
    }

    if do_code {
        let rcx = RenderCx::new();
        let fragments = render_file(&grammar, &rcx);
        let mut buf = String::new();
        fragments.fmt_write_to(&mut buf, &rcx);
        buf = buf.replace('}', "\n}");
        buf = rustfmt_format(&buf).unwrap();

        print!("\n{buf}");
    }

    print!("{buf}");
    runner.report_errors();

    Ok(())
}

// fn generate_code(code: &CodeFile) -> Result<String, String> {
//     let mut buffer = String::new();
//     code.display(&mut buffer);
//     let result = rustfmt_format(&buffer);
//     result.map_err(|_| buffer)
// }

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
