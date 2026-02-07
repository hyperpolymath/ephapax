// SPDX-License-Identifier: PMPL-1.0-or-later
// VS Code extension for Ephapax language support

import * as vscode from 'vscode';
import * as path from 'path';
import {
    LanguageClient,
    LanguageClientOptions,
    ServerOptions,
    TransportKind
} from 'vscode-languageclient/node';

let client: LanguageClient | undefined;
let statusBarItem: vscode.StatusBarItem;

export function activate(context: vscode.ExtensionContext) {
    console.log('Ephapax extension is now active');

    // Create status bar item for mode display
    statusBarItem = vscode.window.createStatusBarItem(
        vscode.StatusBarAlignment.Right,
        100
    );
    statusBarItem.command = 'ephapax.switchMode';
    updateStatusBar();
    statusBarItem.show();
    context.subscriptions.push(statusBarItem);

    // Register commands
    context.subscriptions.push(
        vscode.commands.registerCommand('ephapax.switchMode', switchMode)
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('ephapax.restartLsp', restartLsp)
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('ephapax.showMode', showMode)
    );

    // Start LSP client
    startLanguageClient(context);
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}

function startLanguageClient(context: vscode.ExtensionContext) {
    const config = vscode.workspace.getConfiguration('ephapax');
    const lspPath = config.get<string>('lsp.path', 'ephapax-lsp');
    const mode = config.get<string>('mode', 'linear');

    const serverOptions: ServerOptions = {
        command: lspPath,
        args: ['--mode', mode],
        transport: TransportKind.stdio
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: 'file', language: 'ephapax' }],
        synchronize: {
            fileEvents: vscode.workspace.createFileSystemWatcher('**/*.eph')
        }
    };

    client = new LanguageClient(
        'ephapax',
        'Ephapax Language Server',
        serverOptions,
        clientOptions
    );

    client.start();
}

async function switchMode() {
    const config = vscode.workspace.getConfiguration('ephapax');
    const currentMode = config.get<string>('mode', 'linear');

    const newMode = currentMode === 'linear' ? 'affine' : 'linear';

    await config.update('mode', newMode, vscode.ConfigurationTarget.Global);

    updateStatusBar();

    // Restart LSP with new mode
    await restartLsp();

    vscode.window.showInformationMessage(
        `Ephapax mode switched to: ${newMode.toUpperCase()}`
    );
}

function updateStatusBar() {
    const config = vscode.workspace.getConfiguration('ephapax');
    const mode = config.get<string>('mode', 'linear');

    const icon = mode === 'linear' ? '$(lock)' : '$(unlock)';
    statusBarItem.text = `${icon} Ephapax [${mode.toUpperCase()}]`;
    statusBarItem.tooltip = `Click to switch to ${mode === 'linear' ? 'affine' : 'linear'} mode`;
}

async function restartLsp() {
    if (client) {
        await client.stop();
        client = undefined;
    }

    // Get the extension context (we need to store it globally)
    const context = (global as any).ephapaxContext;
    if (context) {
        startLanguageClient(context);
        vscode.window.showInformationMessage('Ephapax Language Server restarted');
    }
}

async function showMode() {
    const config = vscode.workspace.getConfiguration('ephapax');
    const mode = config.get<string>('mode', 'linear');

    const modeDescription = mode === 'linear'
        ? 'Linear mode: Values must be used exactly once'
        : 'Affine mode: Values can be used at most once (allows dropping)';

    vscode.window.showInformationMessage(
        `Current Ephapax Mode: ${mode.toUpperCase()}\n${modeDescription}`
    );
}

// Store context globally for restart command
export function setGlobalContext(context: vscode.ExtensionContext) {
    (global as any).ephapaxContext = context;
}
