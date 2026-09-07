// VS Code has no analyzer concept of its own: F# analyzers load through
// Ionide -> FsAutoComplete -> FSharp.Analyzers.SDK, from the directories
// the `FSharp.analyzersPath` setting names. This extension bundles the
// FSharp.Refactor analyzer assemblies (BOTH SDK builds — FSAC loads the
// one matching its own SDK version and skips the other) and, with the
// user's consent, appends its own analyzers directory to that setting.
import * as cp from 'child_process';
import * as vscode from 'vscode';

const SECTION = 'FSharp';
// entries written by ANY version of this extension carry the extension id
// in their path (…/thorium.fsharp-refactor-<version>/analyzers), so stale
// versions can be recognized and replaced on update
const PATH_MARKER = '.fsharp-refactor-';
const DECLINED_KEY = 'fsharpRefactor.wireDeclined';

function analyzersDir(context: vscode.ExtensionContext): string {
    return vscode.Uri.joinPath(context.extensionUri, 'analyzers').fsPath;
}

/// The GLOBAL analyzersPath, never the effective one.
///
/// `getConfiguration().get()` merges workspace over global, so a workspace
/// that sets its own analyzersPath HIDES the entry this extension maintains -
/// the stale-version repair then sees nothing to repair and silently leaves
/// the old, now deleted, extension folder in place. Every decision about the
/// entry we own has to look at the global scope directly.
function globalAnalyzersPath(): string[] {
    return vscode.workspace.getConfiguration(SECTION).inspect<string[]>('analyzersPath')?.globalValue ?? [];
}

async function promptReload(message: string): Promise<void> {
    const pick = await vscode.window.showInformationMessage(message, 'Reload Window');
    if (pick === 'Reload Window') {
        await vscode.commands.executeCommand('workbench.action.reloadWindow');
    }
}

async function wire(context: vscode.ExtensionContext, interactive: boolean): Promise<void> {
    const config = vscode.workspace.getConfiguration(SECTION);
    const dir = analyzersDir(context);
    const current = globalAnalyzersPath();

    // replace entries from older versions of this extension, keep the rest
    const kept = current.filter(p => !p.includes(PATH_MARKER));
    const wired = current.includes(dir);
    const enabled = config.get<boolean>('enableAnalyzers') ?? false;

    if (wired && enabled) {
        if (interactive) {
            vscode.window.showInformationMessage('FSharp.Refactor analyzers are already wired into Ionide.');
        }
        return;
    }

    await config.update('analyzersPath', [...kept, dir], vscode.ConfigurationTarget.Global);
    if (!enabled) {
        await config.update('enableAnalyzers', true, vscode.ConfigurationTarget.Global);
    }

    await context.globalState.update(DECLINED_KEY, undefined);
    await promptReload('FSharp.Refactor analyzers wired into Ionide. Reload to activate?');
}

async function unwire(context: vscode.ExtensionContext): Promise<void> {
    const config = vscode.workspace.getConfiguration(SECTION);
    const current = globalAnalyzersPath();
    const kept = current.filter(p => !p.includes(PATH_MARKER));

    if (kept.length === current.length) {
        vscode.window.showInformationMessage('FSharp.Refactor analyzers were not wired.');
        return;
    }

    await config.update('analyzersPath', kept.length > 0 ? kept : undefined, vscode.ConfigurationTarget.Global);
    // leave enableAnalyzers alone: the user may have other analyzers
    await context.globalState.update(DECLINED_KEY, true);
    await promptReload('FSharp.Refactor analyzers removed from Ionide settings. Reload to apply?');
}

// the extension shipped under this id before it moved publishers; both
// installed side by side register the same commands, and the second one
// to activate threw in registerCommand — before it could re-point the
// analyzers setting, which is how a machine kept running the old build
const PREVIOUS_ID = 'thorium.fsharp-refactor';

async function retirePrevious(): Promise<void> {
    const previous = vscode.extensions.getExtension(PREVIOUS_ID);
    if (!previous) {
        return;
    }

    const pick = await vscode.window.showWarningMessage(
        `FSharp.Refactor: an older copy (${PREVIOUS_ID}) is installed beside this one and competes for the same settings. Uninstall it?`,
        'Uninstall old copy',
        'Keep both'
    );

    if (pick === 'Uninstall old copy') {
        try {
            await vscode.commands.executeCommand('workbench.extensions.uninstallExtension', PREVIOUS_ID);
            await promptReload('Old FSharp.Refactor copy removed. Reload to finish?');
        } catch (error) {
            vscode.window.showErrorMessage(`FSharp.Refactor: could not uninstall ${PREVIOUS_ID}: ${String(error)}`);
        }
    }
}

// ---- the apply tool: fsharp-refactor as a dotnet global tool ----

const TOOL = 'fsharp-refactor';

/// The tool's version, or undefined when it is not on the PATH.
function toolVersion(): Promise<string | undefined> {
    return new Promise(resolve => {
        cp.execFile(TOOL, ['--version'], { timeout: 15000 }, (error, stdout) => {
            if (error) {
                resolve(undefined);
            } else {
                resolve(String(stdout).trim());
            }
        });
    });
}

async function exists(uri: vscode.Uri): Promise<boolean> {
    try {
        await vscode.workspace.fs.stat(uri);
        return true;
    } catch {
        return false;
    }
}

let terminal: vscode.Terminal | undefined;

function toolTerminal(): vscode.Terminal {
    if (!terminal || terminal.exitStatus) {
        terminal = vscode.window.createTerminal(TOOL);
    }
    return terminal;
}

/// Everything a "why do I see no hints?" question needs, in one place:
/// the extension, its analyzers, the wiring, Ionide and its FSAC, the tool.
async function status(context: vscode.ExtensionContext): Promise<void> {
    const pkg = context.extension.packageJSON as {
        version?: string;
        fsharpRefactorBuild?: { analyzers?: string; built?: string };
    };
    const config = vscode.workspace.getConfiguration(SECTION);
    const dir = analyzersDir(context);
    const paths = config.get<string[]>('analyzersPath') ?? [];
    const enabled = config.get<boolean>('enableAnalyzers') ?? false;
    const ionide = vscode.extensions.getExtension('ionide.ionide-fsharp');
    const ionideVersion = (ionide?.packageJSON as { version?: string } | undefined)?.version;
    const fsacSetting = config.get<string>('fsac.netCoreDllPath');
    const fsacBundled = ionide ? vscode.Uri.joinPath(ionide.extensionUri, 'bin', 'fsautocomplete.dll') : undefined;
    const fsacPath = fsacSetting && fsacSetting.length > 0
        ? fsacSetting
        : fsacBundled && (await exists(fsacBundled)) ? fsacBundled.fsPath : '(not found)';
    const stale = paths.filter(p => p.includes(PATH_MARKER) && p !== dir);
    const tool = await toolVersion();

    const lines = [
        `FSharp.Refactor extension ${pkg.version ?? '?'} (${context.extension.id})`,
        `Analyzers ${pkg.fsharpRefactorBuild?.analyzers ?? '?'}, built ${pkg.fsharpRefactorBuild?.built || '?'}`,
        `  ${dir} ${(await exists(vscode.Uri.file(dir))) ? '(present)' : '(MISSING)'}`,
        `Wired into Ionide: ${paths.includes(dir) ? 'yes' : 'NO'}; FSharp.enableAnalyzers: ${enabled}`,
        ...(stale.length > 0 ? [`  stale entries from older versions: ${stale.join(', ')}`] : []),
        `Ionide ${ionideVersion ?? '(not installed)'}; FsAutoComplete: ${fsacPath}`,
        `Apply tool (${TOOL}): ${tool ?? 'not installed — dotnet tool install -g fsharp-refactor'}`,
        `Older copy (${PREVIOUS_ID}): ${vscode.extensions.getExtension(PREVIOUS_ID) ? 'STILL INSTALLED' : 'not installed'}`,
    ];

    const channel = vscode.window.createOutputChannel('FSharp.Refactor');
    channel.clear();
    for (const line of lines) {
        channel.appendLine(line);
    }
    channel.show(true);

    const problems = [
        ...(paths.includes(dir) && enabled ? [] : ['analyzers not wired']),
        ...(stale.length > 0 ? ['stale entries'] : []),
        ...(tool ? [] : ['tool not installed']),
    ];
    vscode.window.showInformationMessage(
        problems.length === 0
            ? `FSharp.Refactor ${pkg.version ?? ''}: everything wired (details in the Output panel).`
            : `FSharp.Refactor ${pkg.version ?? ''}: ${problems.join(', ')} (details in the Output panel).`
    );
}

/// The solution or project to work on: the only one there is, or the
/// user's pick when the workspace holds several.
async function pickTarget(): Promise<vscode.Uri | undefined> {
    const folders = vscode.workspace.workspaceFolders ?? [];
    if (folders.length === 0) {
        vscode.window.showWarningMessage('FSharp.Refactor: open a folder or workspace first.');
        return undefined;
    }

    const found = await vscode.workspace.findFiles(
        '**/*.{sln,slnx,fsproj}',
        '**/{node_modules,bin,obj,packages,paket-files,.git}/**',
        100
    );

    /// The TOOL takes a script or a whole directory as happily as a project -
    /// a folder of loose .fsx has always worked on the command line. Only this
    /// picker ever insisted on a project file, which made "open folder" and a
    /// lone script look unsupported when they are not.
    const active = vscode.window.activeTextEditor?.document.uri;
    const activeScript = active && /\.(fsx|fsscript)$/i.test(active.fsPath) ? active : undefined;

    if (found.length === 0) {
        // the folder itself: the tool sweeps the scripts inside it
        return activeScript ?? folders[0].uri;
    }

    const rank = (u: vscode.Uri) => (u.fsPath.endsWith('.fsproj') ? 1 : 0);
    const projects = found.sort((a, b) => rank(a) - rank(b) || a.fsPath.localeCompare(b.fsPath));

    // an open script is a legitimate target even in a workspace full of
    // projects, and it is the one the user is looking at
    const targets = activeScript ? [activeScript, ...projects] : projects;
    if (targets.length === 1) {
        return targets[0];
    }

    const pick = await vscode.window.showQuickPick(
        targets.map(u => ({ label: vscode.workspace.asRelativePath(u), uri: u })),
        { placeHolder: 'Solution, project or script to run fsharp-refactor on' }
    );
    return pick?.uri;
}

/// The tool has to be on PATH before a terminal line is worth sending;
/// offer the install when it is not.
async function ensureTool(): Promise<boolean> {
    if (await toolVersion()) {
        return true;
    }

    const pick = await vscode.window.showWarningMessage(
        'FSharp.Refactor: the fsharp-refactor dotnet tool is not installed.',
        'Install it'
    );
    if (pick === 'Install it') {
        const t = toolTerminal();
        t.show();
        t.sendText('dotnet tool install -g fsharp-refactor');
    }
    return false;
}

/// Send one tool invocation to the integrated terminal.
async function invoke(args: string): Promise<void> {
    const target = await pickTarget();
    if (!target || !(await ensureTool())) {
        return;
    }

    const t = toolTerminal();
    t.show();
    t.sendText(`${TOOL} "${target.fsPath}" ${args}`.trim());
}

/// Run the apply tool on a solution or project of this workspace, in the
/// integrated terminal: report only by default, the real thing on request.
async function run(): Promise<void> {
    const mode = await vscode.window.showQuickPick(
        [
            { label: 'Report only', description: '--dry-run: list the fixes, change nothing', args: '--dry-run' },
            { label: 'Apply fixes', description: 'rewrite the files; every pass is build-verified and rolled back on error', args: '' },
            { label: 'Apply fixes with --api-changes', description: 'also public signatures, names and cross-file rewrites', args: '--api-changes' },
        ],
        { placeHolder: 'How to run fsharp-refactor' }
    );
    if (!mode) {
        return;
    }

    await invoke(mode.args);
}

/// --api-changes without the mode prompt. It widens which rules fire at
/// all (scope-gated rules skip public declarations otherwise), so it is
/// worth its own palette entry rather than a step inside another flow.
async function runApiChanges(): Promise<void> {
    const pick = await vscode.window.showQuickPick(
        [
            { label: 'Report only', description: '--dry-run --api-changes: change nothing', args: '--dry-run --api-changes' },
            {
                label: 'Apply fixes',
                description: 'rewrites public signatures, names and call sites project-wide',
                args: '--api-changes',
            },
        ],
        { placeHolder: 'fsharp-refactor --api-changes: this rewrites your public surface' }
    );
    if (!pick) {
        return;
    }

    await invoke(pick.args);
}

/// A SARIF file of every finding, for code scanning or a second pass as a
/// --baseline. Always a dry run: a report describes the code as it stands.
async function report(): Promise<void> {
    const folder = vscode.workspace.workspaceFolders?.[0];
    const suggested = folder ? vscode.Uri.joinPath(folder.uri, 'fsharp-refactor.sarif').fsPath : 'fsharp-refactor.sarif';

    const path = await vscode.window.showInputBox({
        prompt: 'Write the SARIF report to',
        value: suggested,
        // .csv and .html are the other two shapes --report knows
        placeHolder: 'a .sarif, .csv or .html path',
    });
    if (!path) {
        return;
    }

    await invoke(`--dry-run --notes --report "${path}"`);
}

/// Run the tool to completion, reporting progress and letting the user
/// cancel. The other commands send a line to the terminal and forget it;
/// these two need to know when it finished, because there is a file to
/// open afterwards.
type ToolRun = { cancelled?: true; failure?: string; output: string };

function runToCompletion(args: string[], title: string): Thenable<ToolRun> {
    return vscode.window.withProgress(
        { location: vscode.ProgressLocation.Notification, title, cancellable: true },
        (_progress, token) =>
            new Promise<ToolRun>(resolve => {
                const child = cp.execFile(
                    TOOL,
                    args,
                    // a solution-wide notes pass is minutes of work on a
                    // large repository; Deedle's 16 compilations took five
                                        // NO shell: with `shell: true` Node joins argv into one
                    // command line WITHOUT quoting, so any workspace path
                    // holding a space ("Visual Studio 18", "Program Files")
                    // arrives split, and one holding & ( ) ` $ arrives as
                    // something else entirely. execFile finds the tool on
                    // PATH by itself.
                    { timeout: 45 * 60 * 1000, maxBuffer: 32 * 1024 * 1024 },
                    (error, stdout, stderr) => {
                        const output = String(stdout ?? '');

                        if (token.isCancellationRequested) {
                            resolve({ cancelled: true, output });
                        } else if (error) {
                            resolve({
                                failure: String(stderr || stdout || error.message).trim() || 'the tool failed',
                                output,
                            });
                        } else {
                            resolve({ output });
                        }
                    }
                );

                token.onCancellationRequested(() => child.kill());
            })
    );
}

/// Write a fsharprefactor.json of the current defaults and open it — or
/// open the one already there.
///
/// The configuration is where publicApi, apiChanges, ignorePaths,
/// suppressions and every rule's default live, and none of that is
/// discoverable by guessing the file exists.
async function createConfig(): Promise<void> {
    const folder = vscode.workspace.workspaceFolders?.[0];
    if (!folder) {
        vscode.window.showWarningMessage('FSharp.Refactor: open a folder or workspace first.');
        return;
    }

    const configPath = vscode.Uri.joinPath(folder.uri, 'fsharprefactor.json');

    // an existing config holds someone's decisions: open it, never offer to
    // replace it. The tool refuses to overwrite for the same reason.
    if (!(await exists(configPath))) {
        if (!(await ensureTool())) {
            return;
        }

        const run = await runToCompletion(
            ['--create-config', folder.uri.fsPath],
            'FSharp.Refactor: writing fsharprefactor.json'
        );

        if (run.cancelled) {
            return;
        }

        if (run.failure) {
            vscode.window.showErrorMessage(`FSharp.Refactor: ${run.failure}`);
            return;
        }

        vscode.window.showInformationMessage(
            'FSharp.Refactor: wrote fsharprefactor.json — every rule at its current default, so it changes nothing until you edit it.'
        );
    }

    await vscode.window.showTextDocument(await vscode.workspace.openTextDocument(configPath));
}

/// The advisory findings as a page, in the browser.
///
/// These are the findings that carry no fix — the rule's whole product is
/// the observation — so unlike everything else the tool does, they are only
/// worth anything if a person reads them. A SARIF file is for CI; this is
/// for the reader.
async function reviewNotes(): Promise<void> {
    const target = await pickTarget();
    if (!target || !(await ensureTool())) {
        return;
    }

    const folder = vscode.workspace.workspaceFolders?.[0];

    const out = folder
        ? vscode.Uri.joinPath(folder.uri, 'fsharp-refactor-notes.html').fsPath
        : 'fsharp-refactor-notes.html';

    const run = await runToCompletion(
        ['--dry-run', '--notes', 'only', '--report', out, target.fsPath],
        'FSharp.Refactor: collecting advisory notes (nothing is written to your code)'
    );

    if (run.cancelled) {
        return;
    }

    if (run.failure) {
        vscode.window.showErrorMessage(`FSharp.Refactor: ${run.failure}`);
        return;
    }

    // the page is written even when it holds nothing, so the run's own
    // count is what says whether there is anything to read
    if (/\b0 finding\(s\) written\b/.test(run.output)) {
        vscode.window.showInformationMessage('FSharp.Refactor: no advisory notes to review.');
        return;
    }

    await vscode.env.openExternal(vscode.Uri.file(out));
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
    // the older copy may already hold these command ids: registration is
    // best effort, and never stops the wiring below
    for (const [id, handler] of [
        ['fsharpRefactor.enable', () => wire(context, true)],
        ['fsharpRefactor.disable', () => unwire(context)],
        ['fsharpRefactor.status', () => status(context)],
        ['fsharpRefactor.run', () => run()],
        ['fsharpRefactor.runApiChanges', () => runApiChanges()],
        ['fsharpRefactor.report', () => report()],
        ['fsharpRefactor.createConfig', () => createConfig()],
        ['fsharpRefactor.reviewNotes', () => reviewNotes()],
    ] as const) {
        try {
            context.subscriptions.push(vscode.commands.registerCommand(id, handler));
        } catch {
            // already registered by the older copy; its handler serves both
        }
    }

    void retirePrevious();

    const config = vscode.workspace.getConfiguration(SECTION);
    const current = globalAnalyzersPath();
    const dir = analyzersDir(context);
    const staleEntry = current.some(p => p.includes(PATH_MARKER) && p !== dir);

    if (current.includes(dir) && (config.get<boolean>('enableAnalyzers') ?? false) && !staleEntry) {
        return; // already wired to THIS version
    }

    if (staleEntry) {
        // an update: the old path is dead, re-point without asking again
        await wire(context, false);
        return;
    }

    if (context.globalState.get<boolean>(DECLINED_KEY)) {
        return; // the user said no; the command remains available
    }

    // settings are the user's — ask before touching them
    const pick = await vscode.window.showInformationMessage(
        'FSharp.Refactor: wire its refactoring analyzers into Ionide? (updates the global FSharp.analyzersPath setting)',
        'Wire it up',
        'Not now'
    );

    if (pick === 'Wire it up') {
        await wire(context, false);
    } else if (pick === 'Not now') {
        await context.globalState.update(DECLINED_KEY, true);
    }
}

export function deactivate(): void {
    // intentionally empty: VS Code offers no reliable uninstall hook, so
    // the settings entry is cleaned up by the update path or the
    // fsharpRefactor.disable command
}
