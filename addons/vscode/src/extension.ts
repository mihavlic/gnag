import {
    type ExtensionContext,
    workspace,
    window,
    commands,
    ViewColumn,
    Uri,
    WorkspaceConfiguration,
} from "vscode";
import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";

import {
    LanguageClient,
    // DidChangeConfigurationNotification,
    type LanguageClientOptions,
    type ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined = undefined;

export function activate(cx: ExtensionContext): Promise<void> {
    const config = workspace.getConfiguration("gnag-lsp");
    const serverCommand = getServer(config);
    const serverOptions: ServerOptions = {
        run: { command: serverCommand, options: { env: { RUST_BACKTRACE: "1" } } },
        debug: { command: serverCommand, options: { env: { RUST_BACKTRACE: "1" } } },
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: "file", language: "gnag" }],
        initializationOptions: config,
    };

    
    client = new LanguageClient("gnag-lsp", "Gnag Language Server", serverOptions, clientOptions);
    
    client.outputChannel.appendLine("running server at '" + serverCommand + "'");
    
    let showAst = registerLspVirtualDocument(cx, client, "showAst");
    let showIr = registerLspVirtualDocument(cx, client, "showIr");
    let showLoweredIr = registerLspVirtualDocument(cx, client, "showLoweredIr");
    cx.subscriptions.push(
        commands.registerCommand("gnag-lsp.restartServer", () => client?.restart()),
        commands.registerCommand("gnag-lsp.showAst", showAst),
        commands.registerCommand("gnag-lsp.showIr", showIr),
        commands.registerCommand("gnag-lsp.showLoweredIr", showLoweredIr),
    );
    
    return client.start();
}

export function deactivate(): Promise<void> | undefined {
    return client?.stop();
}

function getServer(conf: WorkspaceConfiguration): string {
    const pathInConfig = conf.get<string | null>("serverPath");
    if (pathInConfig !== undefined && pathInConfig !== null && fileExists(pathInConfig)) {
        return pathInConfig;
    }
    const windows = process.platform === "win32";
    const suffix = windows ? ".exe" : "";
    const binaryName = "gnag-lsp" + suffix;

    const bundledPath = path.resolve(__dirname, binaryName);

    if (fileExists(bundledPath)) {
        return bundledPath;
    }

    return binaryName;
}

function fileExists(path: string): boolean {
    try {
        fs.accessSync(path);
        return true;
    } catch (error) {
        return false;
    }
}

function sleep(ms: number) {
    return new Promise((resolve) => setTimeout(resolve, ms));
}

const debounce = <T extends (...args: any[]) => any>(
    callback: T,
    waitFor: number
) => {
    let timeout: ReturnType<typeof setTimeout>;
    return (...args: Parameters<T>): ReturnType<T> => {
        let result: any;
        timeout && clearTimeout(timeout);
        timeout = setTimeout(
            () => result = callback(...args),
            waitFor
        );
        return result;
    };
};
  

export function registerLspVirtualDocument(cx: ExtensionContext, client: LanguageClient, command: string): () => void {
    const tdcp = new (class implements vscode.TextDocumentContentProvider {
        readonly uri = vscode.Uri.parse(`gnag-${command}://special`);
        readonly eventEmitter = new vscode.EventEmitter<vscode.Uri>();
        private activeGnagEditor: vscode.TextEditor | null = null;
        private wasEmpty: boolean | null = null;
        constructor() {
            this.onDidChangeActiveTextEditor(vscode.window.activeTextEditor);
            if (this.activeGnagEditor) {
                this.wasEmpty = this.activeGnagEditor.selection.isEmpty;
            }
            vscode.workspace.onDidChangeTextDocument(
                this.onDidChangeTextDocument,
                this,
                cx.subscriptions
            );
            vscode.window.onDidChangeActiveTextEditor(
                this.onDidChangeActiveTextEditor,
                this,
                cx.subscriptions
            );
            vscode.window.onDidChangeTextEditorSelection(
                this.onDidChangeTextEditorSelection,
                this,
                cx.subscriptions
            );
        }

        private onDidChangeTextDocument(event: vscode.TextDocumentChangeEvent) {
            if (event.document.uri === this.activeGnagEditor?.document.uri && event.document.languageId === "gnag") {
                void sleep(30).then(() => this.eventEmitter.fire(this.uri));
            }
        }
        private onDidChangeActiveTextEditor(editor: vscode.TextEditor | undefined) {
            if (editor?.document.languageId !== "gnag") {
                return;
            }

            if (this.activeGnagEditor === null || this.activeGnagEditor.document.uri !== editor.document.uri) {
                this.activeGnagEditor = editor;
                this.eventEmitter.fire(this.uri);
            }
        }
        private onDidChangeTextEditorSelection(editor: vscode.TextEditorSelectionChangeEvent) {
            if (this.activeGnagEditor?.document.uri === editor.textEditor.document.uri) {
                let isEmpty = editor.textEditor.selection.isEmpty;
                if (this.wasEmpty && isEmpty) {
                    return;
                }
                this.wasEmpty = isEmpty;
                this.eventEmitter.fire(this.uri);
            }
        }

        async provideTextDocumentContent(
            uri: vscode.Uri,
            ct: vscode.CancellationToken
        ): Promise<string> {
            if (!this.activeGnagEditor) return "";
            // When the range based query is enabled we take the range of the selection
            client.outputChannel.appendLine(`uri ${uri.query}, ${this.activeGnagEditor.selection.isEmpty}`);
            const range = 
                this.activeGnagEditor.selection.isEmpty
                ? null
                : client.code2ProtocolConverter.asRange(this.activeGnagEditor.selection);
            const params = { textDocument: { uri: this.activeGnagEditor.document.uri.toString() }, range };
            client.outputChannel.appendLine(`LSP ${command} firing!`);
            return client.sendRequest(`gnag-lsp/${command}`, params, ct);
        }

        get onDidChange(): vscode.Event<vscode.Uri> {
            return this.eventEmitter.event;
        }
    });

    cx.subscriptions.push(
        vscode.workspace.registerTextDocumentContentProvider(tdcp.uri.scheme.toString(), tdcp)
    );

    return async () => {
        const editor = vscode.window.activeTextEditor;
        
        // const rangeEnabled = !!editor && !editor.selection.isEmpty;
        client.outputChannel.appendLine(`${command} firing!`);
        // const uri = rangeEnabled ? tdcp.uri.with({query: "range=true"}) : tdcp.uri;
        
        const document = await vscode.workspace.openTextDocument(tdcp.uri);
        tdcp.eventEmitter.fire(tdcp.uri);
        
        void (await vscode.window.showTextDocument(document, {
            viewColumn: vscode.ViewColumn.Two,
            preserveFocus: true,
        }));
    };
}
