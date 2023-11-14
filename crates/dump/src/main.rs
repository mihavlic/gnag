use std::{
    env::args,
    path::{Path, PathBuf},
};

use gnag::{ast::ParsedFile, SpannedError};
use gnag_gen::{
    compile::CompiledFile, convert::ConvertedFile, generate::generate_functions, lower::LoweredFile,
};
use linemap::{LineMap, Utf16Pos};

fn load_from_file() -> Option<(String, PathBuf)> {
    if let Some(file) = args().nth(1) {
        let path = PathBuf::from(file);
        if path.is_file() {
            eprintln!("Compiling grammar from '{}'", path.display());
            let contents = std::fs::read(&path).unwrap();
            let string = String::from_utf8(contents)
                .map_err(|e| e.utf8_error())
                .unwrap();
            return Some((string, path));
        } else {
            eprintln!("'{}' is not a file", path.display());
        }
    }
    eprintln!("No file provided");
    None
}

fn main() {
    let Some((src, file)) = load_from_file() else {
        return;
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
    let compiled = CompiledFile::new(&src, &converted, &lowered);

    let (module, _, errors) = generate_functions(&converted, &lowered, &compiled);
    report(&errors);

    println!("{module}");
    // println!("");
    // println!("{module:#?}");
}
