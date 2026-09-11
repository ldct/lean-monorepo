#!/usr/bin/env python3
"""Warm, alternating A/B benchmarks; also require identical Lean diagnostics."""
import argparse
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import tempfile
import time

project = Path(__file__).resolve().parent.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--stock-project', type=Path, default=project,
                    help='A project with stock Mathlib v4.33.1 cached')
parser.add_argument('--repeat', type=int, default=5)
parser.add_argument('--output', type=Path, default=project / 'benchmark-results.json')
args = parser.parse_args()
stock = Path.home() / '.elan/toolchains/leanprover--lean4---v4.33.1'
fork = project / '.lake/toolchains/lean4/build/release/stage2'


def environment(root, tc):
    env = dict(os.environ)
    for key in list(env):
        if key.startswith('LEAN_') or key in ('DYLD_LIBRARY_PATH', 'LD_LIBRARY_PATH'):
            env.pop(key)
    # Only use Lake for discovery. Run each binary with its own runtime and core oleans.
    env['ELAN_TOOLCHAIN'] = 'leanprover/lean4:v4.33.1' if tc == stock else 'lean-v4.33.1-optimized'
    path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'],
                                   cwd=root, env=env, text=True).strip().split(os.pathsep)
    env['LEAN_PATH'] = os.pathsep.join([str((root / p).resolve()) for p in path[:-1]]
                                      + [str(tc / 'lib/lean')])
    if tc == fork:
        env['LEAN_SEARCH_INDEX_CACHE_DIR'] = str(project / '.lake/optimization-cache/search')
        env['LEAN_TACTIC_INDEX_DIR'] = str(project / '.lake/optimization-cache/tactics')
    return env

configs = {
    'stock': (stock / 'bin/lean', environment(args.stock_project.resolve(), stock)),
    'optimized': (fork / 'bin/lean', environment(project, fork)),
    'optimized-disabled': (fork / 'bin/lean', {**environment(project, fork),
        **{key: '0' for key in ['LEAN_MMAP_RESERVE', 'LEAN_NO_TOUCH', 'LEAN_LAZY_PARTS',
                                'LEAN_SEARCH_INDEX', 'LEAN_TACTIC_INDEX']}}),
}
cases = {
    'import': project / 'scripts/Import.lean',
    'exact': project / 'scripts/Exact.lean',
    'scratch': project / 'Playground/Scratch.lean',
    'tactics': project / 'scripts/Tactics.lean',
    'module': project / 'scripts/Module.lean',
}


def run(binary, env, path):
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        start = time.perf_counter()
        pid = os.posix_spawn(str(binary), [str(binary), str(path)], env,
                            file_actions=[(os.POSIX_SPAWN_DUP2, out.fileno(), 1),
                                          (os.POSIX_SPAWN_DUP2, err.fileno(), 2)])
        _, status, usage = os.wait4(pid, 0)
        elapsed = time.perf_counter() - start
        out.seek(0)
        err.seek(0)
        output = (out.read().decode(), err.read().decode(), os.waitstatus_to_exitcode(status))
        if output[2]:
            raise RuntimeError(f'{binary}: {path}: {output}')
        return dict(wall_s=elapsed, cpu_s=usage.ru_utime + usage.ru_stime,
                    maxrss_bytes=usage.ru_maxrss * (1 if platform.system() == 'Darwin' else 1024)), output

os.chdir(project)
results = {'machine': platform.platform(), 'processor': subprocess.check_output(
    ['sysctl', '-n', 'machdep.cpu.brand_string'], text=True).strip(),
    'memory_bytes': int(subprocess.check_output(['sysctl', '-n', 'hw.memsize'])),
    'repeat': args.repeat, 'cases': {}, 'toolchains': {k: str(v[0]) for k, v in configs.items()}}
for case, path in cases.items():
    print(f'Warming and checking equivalence: {case}', flush=True)
    reference = None
    for name, (binary, env) in configs.items():
        _, output = run(binary, env, path)
        if reference is None:
            reference = output
        elif output != reference:
            raise RuntimeError(f'Diagnostics differ: {case}, {name}\n{reference}\n{output}')
    rows = {name: [] for name in configs}
    for repeat in range(args.repeat):
        order = list(configs)
        if repeat % 2:
            order.reverse()
        for name in order:
            binary, env = configs[name]
            metrics, output = run(binary, env, path)
            if output != reference:
                raise RuntimeError(f'Diagnostics changed during timing: {case}, {name}')
            rows[name].append(metrics)
    summary = {name: {key: statistics.median(row[key] for row in values)
                      for key in values[0]} for name, values in rows.items()}
    results['cases'][case] = {'runs': rows, 'medians': summary, 'diagnostics_identical': True}
    print(case, json.dumps(summary), flush=True)
    args.output.write_text(json.dumps(results, indent=2) + '\n')
print(f'Saved {args.output}')
