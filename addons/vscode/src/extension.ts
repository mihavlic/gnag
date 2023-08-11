import {
    type ExtensionContext,
    workspace,
    window,
    commands,
    ViewColumn,
    Uri,
    WorkspaceConfiguration,
} from "vscode";
import * as path from "path";
import * as fs from "fs";

import {
    LanguageClient,
    // DidChangeConfigurationNotification,
    type LanguageClientOptions,
    type ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined = undefined;

export function activate(context: ExtensionContext): Promise<void> {
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

    context.subscriptions.push(
        commands.registerCommand("gnag-lsp.restartServer", () => client?.restart())
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