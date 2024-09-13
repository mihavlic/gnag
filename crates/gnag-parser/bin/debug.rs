use gnag_parser::LANGUAGE;

fn main() {
    let file = std::env::args().nth(1).expect("No filename provided");
    let contents = std::fs::read_to_string(&file).expect("File doesn't exist");

    let tokens = LANGUAGE.lex_all(contents.as_bytes());
    let trace = LANGUAGE.parse_all(&tokens).to_preorder(&mut Vec::new());

    println!();
    print!("{}", tokens.display(&LANGUAGE, false));
    println!();
    print!("{}", trace.display(&LANGUAGE, false));
}
