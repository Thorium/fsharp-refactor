// VS Code has no analyzer concept of its own: F# analyzers load through
// Ionide -> FsAutoComplete -> FSharp.Analyzers.SDK, from the directories
// the `FSharp.analyzersPath` setting names. This extension bundles the
// FSharp.Refactor analyzers (built for one analyzer SDK; FSAC loads them
// only when its own SDK has the same major.minor) and, with the user's
// consent, appends its own analyzers directory to that setting.
import * as cp from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
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

/// Ionide's own default folders (`packages/Analyzers`, `analyzers`). A
/// user-scope array replaces the default instead of adding to it, so the
/// first entry written there has to carry the defaults along, or every
/// workspace relying on them loses its own analyzers.
function defaultAnalyzersPath(): string[] {
    return vscode.workspace.getConfiguration(SECTION).inspect<string[]>('analyzersPath')?.defaultValue ?? [];
}

const sameEntries = (a: string[], b: string[]) => a.length === b.length && a.every((p, i) => p === b[i]);

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

    // replace entries from older versions of this extension, keep the rest;
    // with nothing else in the user value, the rest is Ionide's default
    const others = current.filter(p => !p.includes(PATH_MARKER));
    const kept = others.length > 0 ? others : defaultAnalyzersPath();
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

    // what is left is Ionide's default, or nothing: the setting goes back to unset
    const restored = kept.length > 0 && !sameEntries(kept, defaultAnalyzersPath()) ? kept : undefined;
    await config.update('analyzersPath', restored, vscode.ConfigurationTarget.Global);
    // leave enableAnalyzers alone: the user may have other analyzers
    await context.globalState.update(DECLINED_KEY, true);
    await promptReload('FSharp.Refactor analyzers removed from Ionide settings. Reload to apply?');
}

// ---- FsAutoComplete: the version the analyzers need ----
//
// The analyzers are built for FSharp.Analyzers.SDK 0.41, which
// FsAutoComplete 0.86.0 and later run. Ionide bundles its own
// FsAutoComplete (Ionide 7: 0.85 and earlier); the
// `FSharp.fsac.netCoreDllPath` setting points it at another one, here the
// fsautocomplete dotnet global tool.

const FSAC_NEEDED: Version = [0, 86, 0];
const FSAC_DECLINED_KEY = 'fsharpRefactor.fsacDeclined';

type Version = [number, number, number];

function parseVersion(text: string): Version | undefined {
    const m = /(\d+)\.(\d+)\.(\d+)/.exec(text);
    return m ? [Number(m[1]), Number(m[2]), Number(m[3])] : undefined;
}

function compareVersions(a: Version, b: Version): number {
    return a[0] - b[0] || a[1] - b[1] || a[2] - b[2];
}

const showVersion = (v: Version | undefined) => (v ? v.join('.') : 'unknown version');

/// Where `dotnet tool install -g` unpacks fsautocomplete: a folder per
/// installed version, `<v>/fsautocomplete/<v>/tools/<tfm>/any/`.
function fsacStore(): string {
    return path.join(process.env.DOTNET_CLI_HOME || os.homedir(), '.dotnet', 'tools', '.store', 'fsautocomplete');
}

const normPath = (s: string) => (process.platform === 'win32' ? path.resolve(s).toLowerCase() : path.resolve(s));

function samePathPrefix(p: string, prefix: string): boolean {
    return normPath(p).startsWith(normPath(prefix) + path.sep);
}

/// A setting value inside the tool store: this extension wrote it (or the
/// user did the same by hand), so it may be re-pointed when the tool moves.
function isStorePath(p: string): boolean {
    return samePathPrefix(p, fsacStore());
}

function readDir(dir: string): string[] {
    try {
        return fs.readdirSync(dir);
    } catch {
        return [];
    }
}

/// The highest .NET runtime major installed, for choosing among the TFM
/// builds of one FsAutoComplete.
function newestRuntimeMajor(): Promise<number | undefined> {
    return new Promise(resolve => {
        cp.execFile('dotnet', ['--list-runtimes'], { timeout: 15000 }, (error, stdout) => {
            const majors = error
                ? []
                : [...String(stdout).matchAll(/^Microsoft\.NETCore\.App (\d+)\./gm)].map(m => Number(m[1]));
            resolve(majors.length > 0 ? Math.max(...majors) : undefined);
        });
    });
}

const tfmMajor = (tfm: string) => Number(/^net(?:coreapp)?(\d+)/.exec(tfm)?.[1] ?? NaN);

/// The newest fsautocomplete in the tool store, as the dll of the highest
/// TFM the installed runtimes can run — the choice the tool's own shim
/// makes. A newer runtime loads an older SDK's MSBuild; the reverse fails.
async function newestStoreFsac(): Promise<{ version: Version; dll: string } | undefined> {
    const runtime = await newestRuntimeMajor();

    const found = readDir(fsacStore())
        .map(v => ({ v, version: parseVersion(v) }))
        .filter((e): e is { v: string; version: Version } => e.version !== undefined)
        .sort((a, b) => compareVersions(b.version, a.version))
        .map(({ v, version }) => {
            const tools = path.join(fsacStore(), v, 'fsautocomplete', v, 'tools');

            const tfm = readDir(tools)
                .filter(t => !Number.isNaN(tfmMajor(t)) && (runtime === undefined || tfmMajor(t) <= runtime))
                .sort((a, b) => tfmMajor(b) - tfmMajor(a))
                .find(t => fs.existsSync(path.join(tools, t, 'any', 'fsautocomplete.dll')));

            return tfm ? { version, dll: path.join(tools, tfm, 'any', 'fsautocomplete.dll') } : undefined;
        })
        .find(e => e !== undefined);

    return found;
}

/// An fsautocomplete.dll inside what `netCoreDllPath` accepts: the dll
/// itself, a folder holding it, or a folder of TFM folders.
function fsacDllIn(p: string): string | undefined {
    if (p.toLowerCase().endsWith('.dll')) {
        return fs.existsSync(p) ? p : undefined;
    }

    return [
        path.join(p, 'fsautocomplete.dll'),
        ...readDir(p)
            .filter(t => t.startsWith('net'))
            .flatMap(t => [path.join(p, t, 'fsautocomplete.dll'), path.join(p, t, 'any', 'fsautocomplete.dll')]),
    ].find(c => fs.existsSync(c));
}

/// What `dotnet fsautocomplete.dll --version` says (a fifth of a second).
function fsacVersionOf(dll: string): Promise<Version | undefined> {
    return new Promise(resolve => {
        cp.execFile('dotnet', [dll, '--version'], { timeout: 15000 }, (error, stdout) =>
            resolve(error ? undefined : parseVersion(String(stdout)))
        );
    });
}

type Fsac = { source: 'setting' | 'bundled'; setting?: string; dll?: string; version?: Version };

/// The FsAutoComplete Ionide runs: the one the setting names, or its own.
async function effectiveFsac(): Promise<Fsac> {
    const setting = vscode.workspace.getConfiguration(SECTION).get<string>('fsac.netCoreDllPath') ?? '';

    if (setting.length > 0) {
        const dll = fsacDllIn(setting);
        return { source: 'setting', setting, dll, version: dll ? await fsacVersionOf(dll) : undefined };
    }

    const ionide = vscode.extensions.getExtension('ionide.ionide-fsharp');
    const dll = ionide ? fsacDllIn(vscode.Uri.joinPath(ionide.extensionUri, 'bin').fsPath) : undefined;
    return { source: 'bundled', dll, version: dll ? await fsacVersionOf(dll) : undefined };
}

const newEnough = (v: Version | undefined) => v !== undefined && compareVersions(v, FSAC_NEEDED) >= 0;

// ---- FsAutoComplete: whether it can load the analyzers ----
//
// FSharp.Analyzers.SDK loads an analyzer assembly only when it was built
// against the SDK's own major.minor, and FsAutoComplete only logs the skip.
// An FsAutoComplete on another SDK shows no suggestion at all, so the
// extension never points Ionide at one and says so when Ionide runs one.

/// The analyzer SDK an FsAutoComplete runs, as major.minor, from the
/// deps.json beside its dll; undefined when that cannot be read.
function fsacSdkOf(dll: string | undefined): string | undefined {
    if (!dll) {
        return undefined;
    }

    try {
        const deps = fs.readFileSync(path.join(path.dirname(dll), 'fsautocomplete.deps.json'), 'utf8');
        const m = /"FSharp\.Analyzers\.SDK\/(\d+)\.(\d+)/.exec(deps);
        return m ? `${m[1]}.${m[2]}` : undefined;
    } catch {
        return undefined;
    }
}

/// The analyzer SDKs the bundled analyzers target, stamped into
/// package.json by the packaging script from the project file.
function bundledSdks(context: vscode.ExtensionContext): string[] {
    const pkg = context.extension.packageJSON as { fsharpRefactorBuild?: { sdks?: string } };
    return (pkg.fsharpRefactorBuild?.sdks ?? '').split(/[,\s]+/).filter(s => s.length > 0);
}

/// False only when both sides are known and no bundled build matches.
function sdkLoads(context: vscode.ExtensionContext, dll: string | undefined): boolean {
    const sdk = fsacSdkOf(dll);
    const bundled = bundledSdks(context);
    return sdk === undefined || bundled.length === 0 || bundled.includes(sdk);
}

const noBuildFor = (context: vscode.ExtensionContext, dll: string | undefined) =>
    `it runs FSharp.Analyzers.SDK ${fsacSdkOf(dll)}, and this extension's analyzers are built for ${bundledSdks(context).join(', ')}`;

function globalFsacSetting(): string {
    return vscode.workspace.getConfiguration(SECTION).inspect<string>('fsac.netCoreDllPath')?.globalValue ?? '';
}

async function setGlobalFsac(dll: string | undefined): Promise<void> {
    await vscode.workspace
        .getConfiguration(SECTION)
        .update('fsac.netCoreDllPath', dll, vscode.ConfigurationTarget.Global);
}

/// `dotnet tool update -g` installs the tool when it is missing too.
function updateFsacTool(): Thenable<string | undefined> {
    return vscode.window.withProgress(
        { location: vscode.ProgressLocation.Notification, title: 'FSharp.Refactor: dotnet tool update -g fsautocomplete' },
        () =>
            new Promise<string | undefined>(resolve => {
                cp.execFile(
                    'dotnet',
                    ['tool', 'update', '-g', 'fsautocomplete'],
                    { timeout: 300000 },
                    (error, stdout, stderr) => resolve(error ? `${stderr || stdout || error.message}`.trim() : undefined)
                );
            })
    );
}

/// Install or update the fsautocomplete tool and point Ionide at it.
async function useNewerFsac(context: vscode.ExtensionContext): Promise<void> {
    let newest = await newestStoreFsac();

    if (!newest || !newEnough(newest.version)) {
        const failure = await updateFsacTool();
        if (failure) {
            vscode.window.showErrorMessage(`FSharp.Refactor: installing fsautocomplete failed: ${failure}`);
            return;
        }
        newest = await newestStoreFsac();
    }

    if (!newest || !newEnough(newest.version)) {
        vscode.window.showErrorMessage(
            `FSharp.Refactor: the fsautocomplete tool is ${showVersion(newest?.version)}; the analyzers need ${showVersion(FSAC_NEEDED)} or later.`
        );
        return;
    }

    if (!sdkLoads(context, newest.dll)) {
        vscode.window.showErrorMessage(
            `FSharp.Refactor: the fsautocomplete tool ${showVersion(newest.version)} was left unused: ${noBuildFor(context, newest.dll)}. Update this extension, or install a matching fsautocomplete.`
        );
        return;
    }

    await setGlobalFsac(newest.dll);
    await context.globalState.update(FSAC_DECLINED_KEY, undefined);
    await promptReload(`FSharp.Refactor: Ionide now runs FsAutoComplete ${showVersion(newest.version)}. Reload to restart it?`);
}

/// Back to the FsAutoComplete Ionide bundles.
async function useBundledFsac(context: vscode.ExtensionContext): Promise<void> {
    const setting = globalFsacSetting();
    await context.globalState.update(FSAC_DECLINED_KEY, true);

    if (setting.length === 0 || !isStorePath(setting)) {
        vscode.window.showInformationMessage(
            setting.length === 0
                ? 'FSharp.Refactor: Ionide already runs its bundled FsAutoComplete.'
                : `FSharp.Refactor: FSharp.fsac.netCoreDllPath points at ${setting}, which this extension did not set; left as it is.`
        );
        return;
    }

    await setGlobalFsac(undefined);
    await promptReload("FSharp.Refactor: Ionide is back on its bundled FsAutoComplete. Reload to restart it?");
}

/// On activation: keep a tool-store path alive across `dotnet tool update`
/// (which deletes the old version's folder), hand back to Ionide's own
/// FsAutoComplete once that is as new, and otherwise offer — once — to get
/// one that loads the analyzers.
async function checkFsac(context: vscode.ExtensionContext): Promise<void> {
    const setting = globalFsacSetting();

    if (setting.length > 0) {
        if (!isStorePath(setting)) {
            return; // the user's own FsAutoComplete
        }

        const newest = await newestStoreFsac();
        const ionide = vscode.extensions.getExtension('ionide.ionide-fsharp');
        const bundledDll = ionide ? fsacDllIn(vscode.Uri.joinPath(ionide.extensionUri, 'bin').fsPath) : undefined;
        const bundled = bundledDll ? await fsacVersionOf(bundledDll) : undefined;

        if (
            bundled &&
            newEnough(bundled) &&
            sdkLoads(context, bundledDll) &&
            (!newest || compareVersions(bundled, newest.version) >= 0)
        ) {
            await setGlobalFsac(undefined);
            await promptReload(
                `FSharp.Refactor: Ionide's own FsAutoComplete (${showVersion(bundled)}) now loads the analyzers; switched back to it. Reload?`
            );
        } else if (
            newest &&
            normPath(newest.dll) !== normPath(setting) &&
            sdkLoads(context, newest.dll) &&
            (!fs.existsSync(setting) || newEnough(newest.version))
        ) {
            await setGlobalFsac(newest.dll);
            await promptReload(
                `FSharp.Refactor: the fsautocomplete tool moved to ${showVersion(newest.version)}; Ionide re-pointed. Reload to restart it?`
            );
        } else if (!newest && !fs.existsSync(setting)) {
            await setGlobalFsac(undefined);
            await promptReload('FSharp.Refactor: the fsautocomplete tool is gone; Ionide is back on its bundled one. Reload?');
        }
        return;
    }

    if (context.globalState.get<boolean>(FSAC_DECLINED_KEY)) {
        return;
    }

    const current = await effectiveFsac();
    if (current.source !== 'bundled' || newEnough(current.version) || current.dll === undefined) {
        return;
    }

    const newest = await newestStoreFsac();
    const ready = newest !== undefined && newEnough(newest.version);

    const pick = await vscode.window.showInformationMessage(
        `FSharp.Refactor: Ionide's FsAutoComplete ${showVersion(current.version)} loads none of the analyzers; ` +
            `they need ${showVersion(FSAC_NEEDED)}+ (bundled with Ionide 8). ` +
            (ready
                ? `Point Ionide at the installed fsautocomplete tool ${showVersion(newest!.version)}?`
                : 'Install the fsautocomplete dotnet tool and point Ionide at it?') +
            ' (sets the global FSharp.fsac.netCoreDllPath)',
        ready ? 'Use it' : 'Install and use it',
        'Not now'
    );

    if (pick === 'Use it' || pick === 'Install and use it') {
        await useNewerFsac(context);
    } else if (pick === 'Not now') {
        await context.globalState.update(FSAC_DECLINED_KEY, true);
    }
}

const SDK_WARNED_KEY = 'fsharpRefactor.sdkWarned';

/// Say so, once per FsAutoComplete, when the one Ionide runs cannot load
/// the bundled analyzers: the skip is otherwise only a log line.
async function warnUnloadable(context: vscode.ExtensionContext): Promise<void> {
    const fsac = await effectiveFsac();
    if (sdkLoads(context, fsac.dll)) {
        return;
    }

    const seen = `${showVersion(fsac.version)} ${fsacSdkOf(fsac.dll)}`;
    if (context.globalState.get<string>(SDK_WARNED_KEY) === seen) {
        return;
    }

    await context.globalState.update(SDK_WARNED_KEY, seen);
    vscode.window.showWarningMessage(
        `FSharp.Refactor: no suggestions will show. Ionide runs FsAutoComplete ${showVersion(fsac.version)}: ${noBuildFor(context, fsac.dll)}. ` +
            (fsac.version !== undefined && !newEnough(fsac.version)
                ? `Update Ionide, or run "FSharp.Refactor: Use FsAutoComplete ${showVersion(FSAC_NEEDED)}+".`
                : 'Update this extension.')
    );
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
    const fsac = await effectiveFsac();
    const fsacWhere =
        fsac.source === 'setting'
            ? `${fsac.dll ?? `${fsac.setting} (NO fsautocomplete.dll there)`} (FSharp.fsac.netCoreDllPath)`
            : `${fsac.dll ?? '(not found)'} (bundled with Ionide)`;
    const recent = newEnough(fsac.version);
    const loads = sdkLoads(context, fsac.dll);
    const stale = paths.filter(p => p.includes(PATH_MARKER) && p !== dir);
    const tool = await toolVersion();

    const lines = [
        `FSharp.Refactor extension ${pkg.version ?? '?'} (${context.extension.id})`,
        `Analyzers ${pkg.fsharpRefactorBuild?.analyzers ?? '?'}, built ${pkg.fsharpRefactorBuild?.built || '?'}`,
        `  ${dir} ${(await exists(vscode.Uri.file(dir))) ? '(present)' : '(MISSING)'}`,
        `Wired into Ionide: ${paths.includes(dir) ? 'yes' : 'NO'}; FSharp.enableAnalyzers: ${enabled}`,
        ...(stale.length > 0 ? [`  stale entries from older versions: ${stale.join(', ')}`] : []),
        `Ionide ${ionideVersion ?? '(not installed)'}; FsAutoComplete ${showVersion(fsac.version)}: ${fsacWhere}`,
        loads
            ? `  analyzer SDK ${fsacSdkOf(fsac.dll) ?? '(unknown)'}; analyzers built for ${bundledSdks(context).join(', ') || '(unknown)'}`
            : `  NO ANALYZERS LOAD: ${noBuildFor(context, fsac.dll)}`,
        ...(recent
            ? []
            : [`  the analyzers need FsAutoComplete ${showVersion(FSAC_NEEDED)}+: update Ionide, or run "FSharp.Refactor: Use FsAutoComplete ${showVersion(FSAC_NEEDED)}+"`]),
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
        ...(loads ? [] : ["FsAutoComplete's analyzer SDK has no matching build"]),
        ...(recent ? [] : [`FsAutoComplete older than ${showVersion(FSAC_NEEDED)}`]),
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

/// The tool reads and rewrites the files on disk: an unsaved editor is
/// analysed as it was last saved, and saving it afterwards overwrites the
/// fix or loses the edit. A run that writes saves everything first, asked.
async function savedForWriting(): Promise<boolean> {
    const dirty = vscode.workspace.textDocuments.filter(d => d.isDirty && !d.isUntitled).length;
    if (dirty === 0) {
        return true;
    }

    const pick = await vscode.window.showWarningMessage(
        `FSharp.Refactor rewrites files on disk, and ${dirty} open file(s) have unsaved changes.`,
        { modal: true },
        'Save all and run'
    );

    return pick === 'Save all and run' && (await vscode.workspace.saveAll(false));
}

/// Send one tool invocation to the integrated terminal.
async function invoke(args: string): Promise<void> {
    const target = await pickTarget();
    if (!target || !(await ensureTool())) {
        return;
    }

    if (!args.includes('--dry-run') && !(await savedForWriting())) {
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
        ['fsharpRefactor.useNewerFsac', () => useNewerFsac(context)],
        ['fsharpRefactor.useBundledFsac', () => useBundledFsac(context)],
    ] as const) {
        try {
            context.subscriptions.push(vscode.commands.registerCommand(id, handler));
        } catch {
            // already registered by the older copy; its handler serves both
        }
    }

    void retirePrevious();

    await wireOnActivation(context);

    // FsAutoComplete's version matters only once the analyzers are wired
    if (globalAnalyzersPath().includes(analyzersDir(context))) {
        await checkFsac(context);
        await warnUnloadable(context);
    }
}

async function wireOnActivation(context: vscode.ExtensionContext): Promise<void> {
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
        'FSharp.Refactor: wire its refactoring analyzers into Ionide? (updates the global FSharp.analyzersPath and FSharp.enableAnalyzers settings)',
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
