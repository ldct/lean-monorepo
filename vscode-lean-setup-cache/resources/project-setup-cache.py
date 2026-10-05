#!/usr/bin/env python3
"""Project-local opt-in cache for Lake's editor ``setup-file`` requests.

This is a LAKE shim, not a replacement for an Elan toolchain binary.  Configure it
with LEAN_SETUP_CACHE_PROJECT, LEAN_SETUP_CACHE_REAL_LAKE, and
LEAN_SETUP_CACHE_DIR, normally through serve-with-setup-cache.py.

Hits return without waiting for a throttled background dependency metadata scan.
Detected changes invalidate future hits; already-open workers require a restart.
Toolchain changes in place and external dependencies require manual cache clearing.
"""
import hashlib
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import uuid

VERSION = 2
CONFIG_NAMES = {'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'}


def required(name):
    value = os.environ.get(name)
    if not value:
        raise SystemExit(f'{name} is required; launch through serve-with-setup-cache.py')
    return Path(value).resolve()


PROJECT = required('LEAN_SETUP_CACHE_PROJECT')
REAL_LAKE = required('LEAN_SETUP_CACHE_REAL_LAKE')
CACHE = required('LEAN_SETUP_CACHE_DIR')
GENERATION = CACHE / 'generation.json'
VALIDATION = CACHE / 'validation.json'
LOCK = CACHE / 'validation.lock'
INVALIDATED = CACHE / 'invalidated.json'


def configuration_digest():
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
    source = Path(args[1]).resolve()
    if not inside(source, PROJECT) or source.suffix != '.lean' or not source.is_file():
        return False
    try:
        return json.loads((CACHE / 'configuration.json').read_text())['digest'] == configuration_digest()
    except (OSError, ValueError, KeyError):
        return False


def valid_output(data):
    obj = json.loads(data)
    if not isinstance(obj, dict) or obj.get('dynlibs') != [] or obj.get('plugins') != []:
        return False
    roots = [(PROJECT / '.lake/build').resolve(), (PROJECT / '.lake/packages').resolve()]
    def covered(value):
        if isinstance(value, str):
            resolved = Path(value).resolve()
            return any(inside(resolved, root) for root in roots)
        return isinstance(value, list) and all(covered(item) for item in value)
    return isinstance(obj.get('importArts'), dict) and all(covered(value) for value in obj['importArts'].values())


def stat_id(path):
    st = path.stat()
    return [st.st_mode, st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns]


def dependency_snapshot():
    """Metadata-only tree snapshot, including directory membership for additions/removals."""
    # Do not scan editable source text: the parsed unsaved header is already a key.
    # Local rebuilt artifacts and every pinned dependency tree cover the setup inputs.
    roots = [PROJECT / '.lake' / 'build', PROJECT / '.lake' / 'packages']
    result = {}
    try:
        for root in roots:
            if not root.exists():
                result[str(root)] = None
                continue
            def failed(error): raise error
            for directory, names, files in os.walk(root, followlinks=False, onerror=failed):
                names[:] = sorted(n for n in names if n != '.git')
                here = Path(directory)
                if any((here / name).is_symlink() for name in names): return None
                result[str(here)] = stat_id(here)
                for name in sorted(files):
                    path = here / name
                    try: result[str(path)] = stat_id(path)
                    except OSError: return None
        return result
    except OSError:
        return None


def generation():
    try: return json.loads(GENERATION.read_text()).get('value', 0)
    except (OSError, ValueError): return 0


def set_generation(value):
    with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
        json.dump({'value': value}, f); temporary = Path(f.name)
    temporary.replace(GENERATION)


def invalidate():
    try:
        value = generation() + 1; set_generation(value)
        INVALIDATED.write_text(json.dumps({'generation': value, 'time': time.time()}) + '\n')
    except OSError: pass


def validation_interval():
    try: return max(0, float(os.environ.get('LEAN_SETUP_CACHE_VALIDATE_INTERVAL', '60')))
    except ValueError: return 60


def validate(entry_path):
    """Detached validator. It never inherits the language-server stdio pipes."""
    CACHE.mkdir(parents=True, exist_ok=True)
    lock = LOCK.open('a')
    try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        lock.close(); return
    try:
        now = time.time()
        try:
            if now - json.loads(VALIDATION.read_text()).get('time', 0) < validation_interval(): return
        except (OSError, ValueError): pass
        try:
            entry = json.loads(Path(entry_path).read_text())
            if entry.get('generation') != generation(): return
            baseline_name = entry['baseline']
            if not isinstance(baseline_name, str): raise ValueError('invalid baseline')
            baseline = json.loads((CACHE / baseline_name).read_text())
            unchanged = baseline == dependency_snapshot()
        except (OSError, ValueError, KeyError, TypeError):
            unchanged = False
        if not unchanged: invalidate()
        with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
            json.dump({'time': now, 'completed_at': time.time(), 'seconds': time.time() - now,
                       'entry': str(entry_path), 'unchanged': unchanged,
                       'failure': None if unchanged else 'baseline changed or unreadable'}, f)
            temporary = Path(f.name)
        temporary.replace(VALIDATION)
    finally:
        lock.close()


def schedule_validation(path):
    if os.environ.get('LEAN_SETUP_CACHE_BACKGROUND_VALIDATE') == '0':
        return
    try:
        if time.time() - json.loads(VALIDATION.read_text()).get('time', 0) < validation_interval(): return
    except (OSError, ValueError): pass
    env = {k: v for k, v in os.environ.items() if k not in {'PYTHONINSPECT', 'PYTHONSTARTUP'}}
    try:
        subprocess.Popen([sys.executable, str(Path(__file__).resolve()), '--validate', str(path)], env=env,
            stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            start_new_session=True, close_fds=True)
    except OSError: pass


def log(message):
    if os.environ.get('LEAN_EDITOR_SETUP_CACHE_VERBOSE') == '1':
        print(f'[project-setup-cache] {message}', file=sys.stderr, flush=True)


def warn_invalidated():
    try:
        status = json.loads(INVALIDATED.read_text())
        print('[project-setup-cache] dependency/artifact change detected; cached setup was invalidated. '
              'Restart the current Lean worker to use the new dependency state.', file=sys.stderr, flush=True)
        INVALIDATED.unlink()
    except (OSError, ValueError): pass


def record(hit, start):
    try:
        CACHE.mkdir(parents=True, exist_ok=True)
        with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
            json.dump({'hit': hit, 'seconds': time.perf_counter() - start, 'files': 0,
                       'time': time.time(), 'pid': os.getpid()}, f)
            temporary = Path(f.name)
        temporary.replace(CACHE / 'last-request.json')
    except OSError:
        pass


def init():
    CACHE.mkdir(parents=True, exist_ok=True)
    (CACHE / 'configuration.json').write_text(json.dumps({'version': VERSION, 'digest': configuration_digest()}) + '\n')
    if not GENERATION.exists(): set_generation(0)
    print(CACHE / 'configuration.json')


def main():
    if sys.argv[1:] == ['--init']:
        init()
        return 0
    if len(sys.argv) == 3 and sys.argv[1] == '--validate':
        validate(sys.argv[2])
        return 0
    args = sys.argv[1:]
    warn_invalidated()
    if not eligible(args):
        os.execv(str(REAL_LAKE), [str(REAL_LAKE), *args])
    header = sys.stdin.buffer.read()
    start = time.perf_counter()
    try:
        parsed = json.loads(header)
        env = {k: v for k, v in os.environ.items() if k not in {
            '_', 'SHLVL', 'OLDPWD', 'LAKE', 'LEAN_EDITOR_SETUP_CACHE',
            'LEAN_EDITOR_SETUP_CACHE_VERBOSE', 'LEAN_SETUP_CACHE_BACKGROUND_VALIDATE',
            'LEAN_SETUP_CACHE_VALIDATE_INTERVAL'}}
        key = hashlib.sha256(json.dumps(
            [VERSION, configuration_digest(), args, parsed, env], sort_keys=True).encode()).hexdigest()
        path = CACHE / f'{key}.json'
        entry = json.loads(path.read_text())
        data = entry['stdout'].encode()
        if entry['sha256'] != hashlib.sha256(data).hexdigest() or entry.get('generation') != generation() \
                or not isinstance(entry.get('baseline'), str) \
                :
            raise ValueError('digest mismatch')
        log(f'hit; background validation; {time.perf_counter() - start:.3f}s')
        record(True, start); sys.stdout.buffer.write(data); sys.stdout.buffer.flush(); schedule_validation(path)
        return 0
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError):
        pass
    log('miss; running normal Lake setup')
    fill_generation = generation()
    before = dependency_snapshot()
    result = subprocess.run([str(REAL_LAKE), *args], input=header, stdout=subprocess.PIPE)
    if result.returncode == 0:
        try:
            after = dependency_snapshot()
            if valid_output(result.stdout) and before is not None and before == after and fill_generation == generation():
                data = result.stdout.decode()
                baseline_name = f'baseline-{uuid.uuid4().hex}.json'
                entry = {'stdout': data, 'sha256': hashlib.sha256(result.stdout).hexdigest(),
                         'generation': fill_generation, 'baseline': baseline_name}
                CACHE.mkdir(parents=True, exist_ok=True)
                with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
                    json.dump(before, f); baseline_temporary = Path(f.name)
                baseline_temporary.replace(CACHE / baseline_name)
                with tempfile.NamedTemporaryFile(mode='w', dir=CACHE, delete=False) as f:
                    json.dump(entry, f); temporary = Path(f.name)
                temporary.replace(path)
        except (OSError, ValueError, UnicodeDecodeError):
            pass
    sys.stdout.buffer.write(result.stdout); record(False, start)
    return result.returncode


if __name__ == '__main__':
    sys.exit(main())
