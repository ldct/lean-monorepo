#!/usr/bin/env python3
"""Start a project Lean server with the project-local setup-file cache enabled.

Example stock server (the default):
  python3 scripts/serve-with-setup-cache.py --toolchain leanprover/lean4:v4.33.1

Pass --disable to launch the same server without the shim.  --init is implicit
unless --disable is used; it only records configuration, never scans artifacts.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent.parent
SHIM = Path(__file__).with_name('project-setup-cache.py')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain', help='Elan toolchain name, e.g. leanprover/lean4:v4.33.1')
parser.add_argument('--project', type=Path, default=PROJECT, help='Project root (default: this playground)')
parser.add_argument('--lean', type=Path, help='Explicit Lean executable (requires --lake)')
parser.add_argument('--lake', type=Path, help='Explicit real Lake executable')
parser.add_argument('--cache-dir', type=Path, help='Default: .lake/editor-setup-cache-<toolchain>')
parser.add_argument('--disable', action='store_true', help='Run without the cache shim')
parser.add_argument('server_args', nargs=argparse.REMAINDER,
                    help='Arguments passed through to Lean after the project path')
args = parser.parse_args()
if args.server_args[:1] == ['--']:
    args.server_args = args.server_args[1:]
project = args.project.resolve()

base = dict(os.environ)
for name in ('LEAN_SYSROOT', 'LEAN_PATH', 'DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH', 'LAKE'):
    base.pop(name, None)
if args.toolchain:
    base['ELAN_TOOLCHAIN'] = args.toolchain

def output(command):
    return subprocess.check_output(command, cwd=project, env=base, text=True).strip()

lake = args.lake.resolve() if args.lake else Path(output(['elan', 'which', 'lake'])).resolve()
lean = args.lean.resolve() if args.lean else Path(output(['elan', 'which', 'lean'])).resolve()
env = json.loads(subprocess.check_output([str(lake), 'env', 'python3', '-c',
    'import os,json; print(json.dumps(dict(os.environ)))'], cwd=project, env=base, text=True))
for name, value in base.items():
    if name.startswith('LEAN_SETUP_CACHE_') or name.startswith('LEAN_EDITOR_SETUP_CACHE'):
        env[name] = value
if args.disable:
    env.pop('LAKE', None)
else:
    label = (args.toolchain or lean.parent.parent.name).replace('/', '_').replace(':', '_')
    cache = (args.cache_dir or project / '.lake' / f'lean-infoview-setup-cache-{label}').resolve()
    env.update({'LAKE': str(SHIM), 'LEAN_SETUP_CACHE_PROJECT': str(project),
                'LEAN_SETUP_CACHE_REAL_LAKE': str(lake), 'LEAN_SETUP_CACHE_DIR': str(cache)})
    subprocess.run([sys.executable, str(SHIM), '--init'], cwd=project, env=env,
                   stdout=subprocess.DEVNULL, check=True)
os.execve(str(lean), [str(lean), '--server', str(project), *args.server_args], env)
