install:
    cargo install --debug --path crates/gnag-lsp
npm-compile:
    cd addons/vscode; npm run compile
build: install npm-compile