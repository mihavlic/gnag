dump-dot-watch file:
    watchexec --no-discover-ignore -w {{file}} just dump-dot {{file}}
dump-dot file:
    cargo run --bin dump -- --dot {{file}} > target/dump || true
    dot target/dump -T pdf -o target/dot.pdf
npm-compile:
    cd addons/vscode
    npm run compile
install:
    cargo install --debug --path crates/gnag-lsp
build: npm-compile install