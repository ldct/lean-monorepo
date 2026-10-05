#!/usr/bin/env python3
"""Benchmark real stock/selected LSP setup caching with an unsaved module header."""
import argparse
import json
import os
from pathlib import Path
import statistics
import sys
import time

PROJECT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT / '.lake/toolchains/lean-optimizations/code/benchmarks/interactive'))
from lspbench import LeanLsp

parser = argparse.ArgumentParser()
parser.add_argument('--toolchain', default='leanprover/lean4:v4.33.1')
parser.add_argument('--repeat', type=int, default=3)
parser.add_argument('--ordinary-header', action='store_true',
                    help='Use Scratch as-is; default prepends an unsaved module header')
parser.add_argument('--output', type=Path, default=PROJECT / '.lake/infoview-investigation/stock-module-setup-cache.json')
args = parser.parse_args()
SERVER = [sys.executable, str(PROJECT / 'scripts/serve-with-setup-cache.py'), '--toolchain', args.toolchain]
SOURCE = PROJECT / 'Playground/Scratch.lean'
TEXT = SOURCE.read_text() if args.ordinary_header else 'module\n' + SOURCE.read_text()
URI = SOURCE.resolve().as_uri()
CACHE = PROJECT / '.lake/editor-setup-cache-leanprover_lean4_v4.33.1'

def setup_request_after(start):
    try:
        row = json.loads((CACHE / 'last-request.json').read_text())
        return row if row.get('time', 0) >= start else None
    except (OSError, ValueError): return None

def goal_and_interactive(c, text, version):
    line = next(i for i, row in enumerate(text.splitlines()) if row.strip() == 'linarith')
    params = {'textDocument': {'uri': URI}, 'position': {'line': line, 'character': 2}}
    goal = c.request('$/lean/plainGoal', params)
    session = c.request('$/lean/rpc/connect', {'uri': URI})['result']['sessionId']
    interactive = c.request('$/lean/rpc/call', {**params, 'sessionId': session,
      'method': 'Lean.Widget.getInteractiveGoals', 'params': params})
    assert 'x + y' in json.dumps(goal) and interactive.get('result'), (goal, interactive)

def run(label, enabled, verify_edits=False, expect_hit=True):
    out = PROJECT / '.lake/infoview-investigation' / 'stock-module-cache-raw' / f'{label}-{time.time_ns()}'
    out.mkdir(parents=True)
    command = SERVER if enabled else [*SERVER, '--disable']
    env = dict(os.environ); env['LEAN_EDITOR_SETUP_CACHE_VERBOSE'] = '1'
    c = LeanLsp(command, PROJECT, env, out)
    try:
        request_start = time.time(); begin = c.now()
        c.request('initialize', {'processId': os.getpid(), 'rootUri': PROJECT.as_uri(),
          'capabilities': {'textDocument': {'publishDiagnostics': {'versionSupport': True}}},
          'initializationOptions': {'hasWidgets': True, 'editDelay': 0}})
        initialized = c.now(); c.notify('initialized', {})
        c.notify('textDocument/didOpen', {'textDocument': {'uri': URI, 'languageId': 'lean',
          'version': 1, 'text': TEXT}, 'dependencyBuildMode': 'never'})
        done = c.wait_progress_done(URI, 1, 120, min_t=initialized)
        assert done is not None and not c.progress[URI].get('fatal'), c.diags
        goal_and_interactive(c, TEXT, 1)
        row = {'label': label, 'startup_s': initialized - begin, 'open_s': done - initialized,
               'setup_cache_hit': None}
        request = setup_request_after(request_start) if enabled else None
        if request is not None: row['setup_cache_hit'] = request.get('hit')
        if enabled and expect_hit: assert row['setup_cache_hit'] is True, row
        if verify_edits:
            bad = TEXT + '\nexample : False := by trivial\n'
            c.notify('textDocument/didChange', {'textDocument': {'uri': URI, 'version': 2}, 'contentChanges': [{'text': bad}]})
            assert c.wait_progress_done(URI, 2, 120, min_t=c.now()) is not None
            assert any(d.get('severity') == 1 for d in c.diags[URI]['diagnostics']), c.diags
            c.notify('textDocument/didChange', {'textDocument': {'uri': URI, 'version': 3}, 'contentChanges': [{'text': TEXT}]})
            assert c.wait_progress_done(URI, 3, 120, min_t=c.now()) is not None
            goal_and_interactive(c, TEXT, 3)
            missing = TEXT.replace('import Mathlib', 'import MissingModuleForSetupCache')
            c.notify('textDocument/didChange', {'textDocument': {'uri': URI, 'version': 4}, 'contentChanges': [{'text': missing}]})
            assert c.wait_progress_done(URI, 4, 120, min_t=c.now()) is not None
            assert any(d.get('severity') == 1 for d in c.diags[URI]['diagnostics']), c.diags
            c.notify('textDocument/didChange', {'textDocument': {'uri': URI, 'version': 5}, 'contentChanges': [{'text': TEXT}]})
            assert c.wait_progress_done(URI, 5, 120, min_t=c.now()) is not None
            goal_and_interactive(c, TEXT, 5)
        print(json.dumps(row), flush=True); return row
    finally: c.close()

# The first enabled launch fills its entry and is excluded from the warm comparison.
warmup = run('cache-fill', True, expect_hit=False)
checks = run('cache-edit-check', True, verify_edits=True)
rows = {'stock_module_uncached': [], 'stock_module_cached': []}
for rep in range(args.repeat):
    order = [('stock_module_uncached', False), ('stock_module_cached', True)]
    if rep % 2: order.reverse()
    for label, enabled in order: rows[label].append(run(f'{label}-{rep + 1}', enabled))
summary = {label: {field: statistics.median(r[field] for r in values) for field in ('startup_s', 'open_s')}
           for label, values in rows.items()}
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps({'warmup': warmup, 'checks': checks, 'runs': rows, 'summary': summary}, indent=2) + '\n')
print(json.dumps(summary, indent=2))
