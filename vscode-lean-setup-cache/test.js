'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const Module = require('node:module');

const root = fs.mkdtempSync(path.join(os.tmpdir(), 'lean-setup-cache-extension-'));
fs.writeFileSync(path.join(root, 'lean-toolchain'), 'leanprover/lean4:stable\n');
fs.writeFileSync(path.join(root, 'lakefile.toml'), '[package]\nname = "fixture"\n');

const ownedPath = '.vscode/lean-setup-cache/bin';
let values = ['existing/bin'];
let trusted = true;
let folders = [{uri: {scheme: 'file', fsPath: root}}];
const commands = new Map();
const messages = {errors: [], info: []};
const state = new Map();
const output = {clear() {}, appendLine() {}, show() {}, dispose() {}};
const vscode = {
  ConfigurationTarget: {Workspace: 2},
  workspace: {
    get isTrusted() { return trusted; },
    get workspaceFolders() { return folders; },
    getConfiguration() {
      return {
        get() { return values; },
        inspect() { return {workspaceValue: values, globalValue: []}; },
        async update(_name, value) { values = value; },
      };
    },
  },
  window: {
    createOutputChannel() { return output; },
    showErrorMessage(message) { messages.errors.push(message); },
    showInformationMessage(message) { messages.info.push(message); },
  },
  commands: {
    registerCommand(name, callback) {
      commands.set(name, callback);
      return {dispose() {}};
    },
  },
};

const originalLoad = Module._load;
Module._load = (request, parent, isMain) => {
  if (request === 'vscode') return vscode;
  if (request === 'node:child_process') {
    return {execFile(_file, _args, _options, callback) { callback(null, '', ''); }};
  }
  return originalLoad(request, parent, isMain);
};
delete require.cache[require.resolve('./extension')];
require('./extension').activate({
  extensionPath: __dirname,
  subscriptions: [],
  workspaceState: {
    get(key, fallback) { return state.has(key) ? state.get(key) : fallback; },
    async update(key, value) { state.set(key, value); },
  },
});
Module._load = originalLoad;

async function invoke(name) {
  messages.errors.length = 0;
  await commands.get(name)();
}

(async () => {
  await invoke('leanSetupCache.enable');
  assert.deepEqual(values, [ownedPath, 'existing/bin']);
  assert(fs.existsSync(path.join(root, '.vscode/lean-setup-cache/bin/lake')));
  assert.equal(messages.errors.length, 0);

  await invoke('leanSetupCache.disable');
  assert.deepEqual(values, ['existing/bin']);
  assert.equal(messages.errors.length, 0);

  trusted = false;
  await invoke('leanSetupCache.enable');
  assert.match(messages.errors[0], /trusted workspace/);

  trusted = true;
  folders = [];
  await invoke('leanSetupCache.status');
  assert.match(messages.errors[0], /one local Lean project folder/);

  console.log('mocked command tests verified settings preservation and unsupported workspaces');
})().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
