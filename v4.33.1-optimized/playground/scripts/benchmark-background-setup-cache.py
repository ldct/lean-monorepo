#!/usr/bin/env python3
"""Alternate stock LSP opens with no cache, unchecked hits, and actively checked hits."""
import argparse
import json
import os
from pathlib import Path
import statistics
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / '.lake/toolchains/lean-optimizations/code/benchmarks/interactive'))
from lspbench import LeanLsp

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path, default=HERE.parents[2] / 'v4.33.1/playground')
p.add_argument('--repeat', type=int, default=3)
a = p.parse_args()
project = a.project.resolve()
assert a.repeat > 0
out = project / '.lake/infoview-investigation' / ('background-review-' + str(time.time_ns()))
out.mkdir(parents=True)
cache = out / 'cache'
source = project / 'Playground/Scratch.lean'
text = source.read_text()
uri = source.as_uri()
command = [sys.executable, str(HERE / 'serve-with-setup-cache.py'), '--project', str(project),
           '--toolchain', 'leanprover/lean4:v4.33.1', '--cache-dir', str(cache)]
rows = []

def run(mode, name, fill=False):
    env = dict(os.environ)
    env['LEAN_SETUP_CACHE_BACKGROUND_VALIDATE'] = '1' if mode == 'checked' else '0'
    env['LEAN_SETUP_CACHE_VALIDATE_INTERVAL'] = '0'
    env['LEAN_EDITOR_SETUP_CACHE_VERBOSE'] = '1'
    raw = out / name
    raw.mkdir()
    client = LeanLsp(command + (['--disable'] if mode == 'uncached' else []), project, env, raw)
    try:
        begin = client.now()
        client.request('initialize', {'processId': os.getpid(), 'rootUri': project.as_uri(),
            'capabilities': {'textDocument': {'publishDiagnostics': {'versionSupport': True}}},
            'initializationOptions': {'hasWidgets': True, 'editDelay': 0}})
        client.notify('initialized', {})
        start = client.now(); wall = time.time()
        client.notify('textDocument/didOpen', {'textDocument': {'uri': uri, 'languageId': 'lean', 'version': 1, 'text': text}, 'dependencyBuildMode': 'never'})
        done = client.wait_progress_done(uri, 1, 120, min_t=start)
        assert done is not None and not client.progress[uri].get('fatal'), client.diags
        assert client.wait_diag_version(uri, 1, 20) is not None
        assert not any(d.get('severity') == 1 for d in client.diags[uri]['diagnostics'])
        params = {'textDocument': {'uri': uri}, 'position': {'line': next(i for i,s in enumerate(text.splitlines()) if s.strip() == 'linarith'), 'character': 2}}
        assert 'x + y' in json.dumps(client.request('$/lean/plainGoal', params))
        session = client.request('$/lean/rpc/connect', {'uri': uri})['result']['sessionId']
        goals = client.request('$/lean/rpc/call', {**params, 'sessionId': session, 'method': 'Lean.Widget.getInteractiveGoals', 'params': params})
        assert 'error' not in goals and goals.get('result'), goals
        row = {'mode': mode, 'name': name, 'startup_s': start-begin, 'open_s': done-start}
        if mode != 'uncached':
            setup = json.loads((cache / 'last-request.json').read_text())
            assert setup['time'] >= wall and setup['hit'] == (not fill), setup
            row['setup'] = setup
        if mode == 'checked':
            deadline = time.monotonic() + 30
            while True:
                try: validation = json.loads((cache / 'validation.json').read_text())
                except (OSError, ValueError): validation = {}
                if validation.get('time', 0) >= wall and validation.get('completed_at', 0) >= wall: break
                assert time.monotonic() < deadline, validation
                time.sleep(.05)
            assert validation['unchanged'], validation
            row['validation'] = validation
        rows.append(row)
        (out / 'results.json').write_text(json.dumps({'runs': rows}, indent=2))
        print(json.dumps(row), flush=True)
    finally:
        client.close()

run('unchecked', 'fill', fill=True)
for rep in range(a.repeat):
    modes = ['uncached', 'unchecked', 'checked']
    modes = modes[rep % 3:] + modes[:rep % 3]
    for mode in modes: run(mode, f'{rep}-{mode}')
summary = {mode: statistics.median(r['open_s'] for r in rows if r['mode'] == mode and r['name'] != 'fill') for mode in ['uncached', 'unchecked', 'checked']}
(out / 'results.json').write_text(json.dumps({'runs': rows, 'median_open_s': summary}, indent=2))
print(json.dumps({'median_open_s': summary, 'results': str(out / 'results.json')}, indent=2))
