'use strict';
const vscode = require('vscode');
const fs = require('node:fs/promises');
const path = require('node:path');
const {execFile} = require('node:child_process');
const {promisify} = require('node:util');
const run = promisify(execFile);
const OWN = '.vscode/lean-setup-cache/bin';
const PREFIX = 'lean-infoview-setup-cache-';

function folder() {
  const folders = vscode.workspace.workspaceFolders || [];
  if (folders.length !== 1 || folders[0].uri.scheme !== 'file') {
    throw new Error('Open one local Lean project folder per window to use this experimental cache.');
  }
  return folders[0].uri.fsPath;
}
async function exists(file) {
  try { await fs.access(file); return true; } catch { return false; }
}
async function project() {
  if (!['darwin', 'linux'].includes(process.platform)) throw new Error('Lean Setup Cache currently supports macOS and Linux.');
  if (!vscode.workspace.isTrusted) throw new Error('Enable caching only in a trusted workspace.');
  const root = folder();
  if (!await exists(path.join(root, 'lean-toolchain')) ||
      !(await exists(path.join(root, 'lakefile.toml')) || await exists(path.join(root, 'lakefile.lean')))) {
    throw new Error('Open the Lean project folder containing lean-toolchain and lakefile.toml or lakefile.lean, rather than its parent folder.');
  }
  return root;
}
async function enable(ctx) {
  const root = await project();
  try {
    await run('python3', ['-c', 'import sys,fcntl; assert sys.version_info >= (3,9)'], {cwd: root});
    await run('elan', ['which', 'lake'], {cwd: root});
  } catch {
    throw new Error('Python 3.9+ and the project’s installed Elan toolchain must be available on PATH before enabling caching.');
  }
  const dest = path.join(root, '.vscode/lean-setup-cache');
  await fs.mkdir(path.join(dest, 'bin'), {recursive: true});
  for (const name of ['project-setup-cache.py', 'serve-with-setup-cache.py']) {
    await fs.copyFile(path.join(ctx.extensionPath, 'resources', name), path.join(dest, name));
    await fs.chmod(path.join(dest, name), 0o755);
  }
  await fs.copyFile(path.join(ctx.extensionPath, 'resources', 'lake'), path.join(dest, 'bin/lake'));
  await fs.chmod(path.join(dest, 'bin/lake'), 0o755);
  const config = vscode.workspace.getConfiguration('lean4');
  const values = config.get('envPathExtensions', []);
  if (!values.includes(OWN)) {
    const previous = config.inspect('envPathExtensions')?.workspaceValue;
    await ctx.workspaceState.update('previousPaths', previous === undefined ? null : previous);
    await config.update('envPathExtensions', [OWN, ...values], vscode.ConfigurationTarget.Workspace);
    await ctx.workspaceState.update('ownsPath', true);
  }
  vscode.window.showInformationMessage('Lean setup caching enabled. Restart the Lean server. The first opening creates the cache; later openings reuse it.');
}
async function disable(ctx) {
  const config = vscode.workspace.getConfiguration('lean4');
  const values = config.get('envPathExtensions', []);
  if (ctx.workspaceState.get('ownsPath', false)) {
    const previous = ctx.workspaceState.get('previousPaths', null);
    const remaining = values.filter(value => value !== OWN);
    // Restore inheritance only if no additional entries were added meanwhile.
    const inherited = config.inspect('envPathExtensions')?.globalValue || [];
    const restore = previous === null && JSON.stringify(remaining) === JSON.stringify(inherited) ? undefined : remaining;
    await config.update('envPathExtensions', restore, vscode.ConfigurationTarget.Workspace);
    await ctx.workspaceState.update('ownsPath', false);
  }
  vscode.window.showInformationMessage('Lean setup caching disabled. Restart the Lean server to use normal Lake setup.');
}
async function caches(root) {
  const dir = path.join(root, '.lake');
  if (!await exists(dir)) return [];
  const entries = await fs.readdir(dir, {withFileTypes: true});
  return entries.filter(e => e.isDirectory() && e.name.startsWith(PREFIX)).map(e => path.join(dir, e.name));
}
async function readJson(file) {
  try { return JSON.parse(await fs.readFile(file, 'utf8')); } catch { return null; }
}
async function clear() {
  const root = await project();
  for (const dir of await caches(root)) {
    const old = await readJson(path.join(dir, 'generation.json'));
    const temporary = path.join(dir, `generation-${process.pid}-${Date.now()}.tmp`);
    await fs.writeFile(temporary, JSON.stringify({value: (old?.value || 0) + 1}));
    await fs.rename(temporary, path.join(dir, 'generation.json'));
  }
  vscode.window.showInformationMessage('Cached setups invalidated. Restart the Lean server; its next opening will recompute setup.');
}
async function status(output) {
  const root = folder();
  const enabled = vscode.workspace.getConfiguration('lean4').get('envPathExtensions', []).includes(OWN);
  output.clear();
  output.appendLine(`Lean Setup Cache: ${enabled ? 'enabled' : 'disabled'} for ${root}`);
  for (const dir of await caches(root)) {
    output.appendLine(path.basename(dir));
    const setup = await readJson(path.join(dir, 'last-request.json'));
    const validation = await readJson(path.join(dir, 'validation.json'));
    if (setup) output.appendLine(`Last setup: ${setup.hit ? 'cache hit' : 'cache fill'}, ${setup.seconds.toFixed(3)} s`);
    if (validation) output.appendLine(`Last background check: ${validation.unchanged ? 'unchanged' : 'changed or unreadable — restart Lean'}, ${new Date((validation.completed_at || validation.time) * 1000).toISOString()}`);
  }
  output.appendLine('Checks run on cache hits, at most once per minute. Already-open workers are not automatically restarted.');
  output.show();
}
function activate(ctx) {
  const output = vscode.window.createOutputChannel('Lean Setup Cache');
  ctx.subscriptions.push(output);
  const commands = {enable: () => enable(ctx), disable: () => disable(ctx), clear, status: () => status(output)};
  for (const [name, action] of Object.entries(commands)) {
    ctx.subscriptions.push(vscode.commands.registerCommand(`leanSetupCache.${name}`, async () => {
      try { await action(); } catch (error) { vscode.window.showErrorMessage(`Lean Setup Cache: ${error.message}`); }
    }));
  }
}
module.exports = {activate};
