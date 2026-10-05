#!/usr/bin/env python3
"""Install (--disable: remove) this playground's editor setup cache."""
import importlib.util
import json
import shlex
import sys
from pathlib import Path

script = Path(__file__).with_name('editor-setup-cache.py')
spec = importlib.util.spec_from_file_location('editor_cache', script)
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)
lake = cache.SYSROOT / 'bin/lake'
real = cache.REAL_LAKE
if '--disable' in sys.argv:
    if real.exists() and lake.read_bytes()[:2] == b'#!':
        real.replace(lake)
    print('Editor setup cache disabled.')
else:
    if lake.read_bytes()[:2] != b'#!':
        # A compiler rebuild may have replaced our wrapper with a newer binary.
        lake.replace(real)
    elif str(script) not in lake.read_text() or not real.exists():
        raise SystemExit('Refusing to replace an unfamiliar or incomplete Lake wrapper.')
    cache.CACHE.mkdir(parents=True, exist_ok=True)
    (cache.CACHE / 'configuration.json').write_text(json.dumps({'digest': cache.configuration_digest()}))
    lake.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' + shlex.quote(str(script)) + ' "$@"\n')
    lake.chmod(0o755)
    print(f'Editor setup cache installed: {lake}')
