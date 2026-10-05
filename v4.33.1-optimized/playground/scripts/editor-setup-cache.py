#!/usr/bin/env python3
"""Setup-file cache without filesystem invalidation for this pinned, local playground.

Only editor requests for Playground/*.lean are eligible. Hits do not scan sources, artifacts or the toolchain. Configuration changes
disable caching until the installer is rerun; other dependency changes require
manually clearing the cache. Everything else goes straight to the real Lake binary.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

PROJECT = Path(__file__).resolve().parent.parent
SYSROOT = PROJECT / '.lake/toolchains/lean4/build/release/stage2'
REAL_LAKE = SYSROOT / 'bin/lake.real'
CACHE = PROJECT / '.lake/editor-setup-cache'
VERSION = 1
CONFIG_NAMES = {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}


def configuration_digest():
    """Lock configuration content, including all pinned dependency configurations."""
    digest = hashlib.sha256()
    roots = [PROJECT]
    packages = PROJECT / '.lake/packages'
    if packages.exists():
        roots.extend(sorted(p for p in packages.iterdir() if p.is_dir()))
    for root in roots:
        for name in sorted(CONFIG_NAMES):
            path = root / name
            digest.update(str(path).encode())
            digest.update(path.read_bytes() if path.is_file() else b'<absent>')
    return digest.hexdigest()


def inside(path, root):
    return path == root or root in path.parents


def eligible(args):
    if os.environ.get('LEAN_EDITOR_SETUP_CACHE') == '0':
        return False
    if len(args) < 3 or args[0] != 'setup-file' or args[2] != '-':
        return False
    if any(a not in {'--no-build', '--no-cache'} for a in args[3:]):
        return False
    if Path.cwd().resolve() != PROJECT:
        return False
    path = Path(args[1]).resolve()
    if not inside(path, PROJECT / 'Playground') or path.suffix != '.lean' or not path.is_file():
        return False
    # Only the installed local dependency search paths are supported.
    for part in os.environ.get('LEAN_PATH', '').split(os.pathsep):
        if part and not inside(Path(part).resolve(), PROJECT):
            return False
    try:
        lock = json.loads((CACHE / 'configuration.json').read_text())
        return lock['digest'] == configuration_digest()
    except (OSError, ValueError, KeyError):
        return False


def valid_output(data):
    obj = json.loads(data)
    if not isinstance(obj, dict) or obj.get('dynlibs') != [] or obj.get('plugins') != []:
        return False
    # Reject external artifact locations, even if a configuration produced them.
    def check(value):
        if isinstance(value, str):
            return os.path.abspath(value).startswith(str(PROJECT) + os.sep)
        return isinstance(value, list) and all(check(v) for v in value)
    return isinstance(obj.get('importArts'), dict) and all(check(v) for v in obj['importArts'].values())


def log(message):
    if os.environ.get('LEAN_EDITOR_SETUP_CACHE_VERBOSE') == '1':
        print(f'[editor-setup-cache] {message}', file=sys.stderr, flush=True)


def record(hit, start, count):
    """Local diagnostics; deliberately contains no environment values."""
    try:
        with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
            json.dump({'hit': hit, 'seconds': time.perf_counter() - start,
                       'files': count, 'time': time.time(), 'pid': os.getpid()}, f)
            temp = Path(f.name)
        temp.replace(CACHE / 'last-request.json')
    except OSError:
        pass


def main():
    args = sys.argv[1:]
    if not eligible(args):
        os.execv(str(REAL_LAKE), [str(REAL_LAKE), *args])
    header = sys.stdin.buffer.read()
    start = time.perf_counter()
    try:
        parsed = json.loads(header)
        if not isinstance(parsed, dict):
            raise ValueError('header is not an object')
        env = {k: v for k, v in os.environ.items() if k not in {
            '_', 'SHLVL', 'OLDPWD', 'LEAN_EDITOR_SETUP_CACHE', 'LEAN_EDITOR_SETUP_CACHE_VERBOSE'}}
        key = hashlib.sha256(json.dumps([VERSION, args, parsed, env], sort_keys=True).encode()).hexdigest()
        path = CACHE / (key + '.json')
        try:
            entry = json.loads(path.read_text())
            if not isinstance(entry, dict) or not isinstance(entry.get('stdout'), str):
                raise ValueError('invalid cache entry')
            data = entry['stdout'].encode()
            if entry['sha256'] == hashlib.sha256(data).hexdigest():
                log(f'hit; no filesystem validation; {time.perf_counter() - start:.3f}s')
                record(True, start, 0)
                sys.stdout.buffer.write(data)
                return 0
        except (OSError, ValueError, KeyError, TypeError):
            pass
    except (OSError, ValueError, RuntimeError):
        # stdin has been consumed, so forward it explicitly on a bypass.
        return subprocess.run([str(REAL_LAKE), *args], input=header).returncode

    log('miss; running normal Lake setup')
    result = subprocess.run([str(REAL_LAKE), *args], input=header, stdout=subprocess.PIPE)
    if result.returncode == 0:
        try:
            if valid_output(result.stdout):
                entry = {'stdout': result.stdout.decode(),
                         'sha256': hashlib.sha256(result.stdout).hexdigest()}
                with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
                    json.dump(entry, f)
                    temp = Path(f.name)
                temp.replace(path)
        except (OSError, ValueError, RuntimeError):
            pass  # cache failure must never turn a successful setup into failure
    sys.stdout.buffer.write(result.stdout)
    record(False, start, 0)
    return result.returncode


if __name__ == '__main__':
    sys.exit(main())
