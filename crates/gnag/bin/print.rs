use std::io::Read;

use gnag::{ast::ParsedFile, file::ConvertedFile, lex, Lexer, Parser};

fn main() {
    // tracy_client::Client::start();
    // profiling::register_thread!("Main Thread");

    let input = if let Some(path) = std::env::args().nth(1) {
        std::fs::read_to_string(path).unwrap()
    } else {
        let mut input = String::new();
        let mut stdin = std::io::stdin().lock();
        _ = stdin.read_to_string(&mut input);
        input
    };

    if input.is_empty() {
        println!("No input provided");
        std::process::exit(-1);
    }

    let mut arena = Vec::new();

    if false {
        let input = input.repeat(10000);

        bench("whole", input.len(), || {
            let mut lexer = Lexer::new(input.as_bytes());
            let (tokens, trivia) = bench("lex", input.len(), || lex(&mut lexer));
            // println!("{tokens:#?}\n{trivia:#?}");
            let mut parser = Parser::new(&input, tokens, trivia);
            bench("parse", input.len(), || gnag::file(&mut parser));
            // println!("Spans {:#?}\nErrors {:#?}", &parser.spans, &parser.errors);
            bench("build", input.len(), || parser.build_tree(&mut arena));
        });
    } else {
        let parsed = ParsedFile::new(&input);
        {
            let pretty = parsed.root.pretty_print_with_file(&input, &parsed);
            println!("{pretty}")
        }
        let convert = ConvertedFile::new(&input, &parsed);

        dbg!(convert.rules);
    }

    // profiling::finish_frame!();
}

fn bench<T>(name: &str, len_bytes: usize, fun: impl FnOnce() -> T) -> T {
    let start = std::time::Instant::now();
    let res = std::hint::black_box(fun());
    let elapsed = start.elapsed().as_secs_f64();

    println!(
        "{name:8} {:.2} ms/MiB",
        (elapsed * 1000.0 * 1024.0 * 1024.0) / len_bytes as f64
    );
    res
}
