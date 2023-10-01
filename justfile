npm-compile:
    cd addons/vscode; npm run compile
install:
    cargo install --debug --path crates/gnag-lsp
build: npm-compile install