#!/usr/bin/env python3
"""Isolated metadata-validator checks for project-setup-cache.py."""
import fcntl, importlib.util, json, os, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
os.environ.update({'LEAN_SETUP_CACHE_PROJECT': str(HERE.parent), 'LEAN_SETUP_CACHE_REAL_LAKE': '/bin/true',
                   'LEAN_SETUP_CACHE_DIR': str(HERE.parent / '.lake/test-cache'), 'LEAN_SETUP_CACHE_VALIDATE_INTERVAL': '0'})
spec = importlib.util.spec_from_file_location('cache', HERE / 'resources/project-setup-cache.py')
c = importlib.util.module_from_spec(spec); spec.loader.exec_module(c)

with tempfile.TemporaryDirectory() as temp:
    root = Path(temp) / 'project'; (root / '.lake/build').mkdir(parents=True); (root / 'Playground').mkdir()
    artifact = root / '.lake/build/A.olean'; artifact.write_text('a')
    proof = root / 'Playground/Scratch.lean'; proof.write_text('example : True := by trivial\n')
    cache = root / '.cache'; cache.mkdir()
    c.PROJECT = root; c.CACHE = cache; c.GENERATION = cache / 'generation.json'; c.VALIDATION = cache / 'validation.json'; c.LOCK = cache / 'validation.lock'; c.INVALIDATED = cache / 'invalidated.json'; c.set_generation(0)
    def entry():
        p = cache / 'entry.json'; p.write_text(json.dumps({'generation': c.generation(), 'baseline': 'baseline.json'})); (cache / 'baseline.json').write_text(json.dumps(c.dependency_snapshot())); return p
    p = entry(); c.validate(p); assert c.generation() == 0
    proof.write_text('example : True := by simp\n'); c.validate(p); assert c.generation() == 0
    artifact.unlink(); artifact.write_text('replacement'); c.validate(p); assert c.generation() == 1
    p = entry(); artifact.unlink(); c.validate(p); assert c.generation() == 2
    p = entry(); (root / '.lake/build/New.olean').write_text('new'); c.validate(p); assert c.generation() == 3
    p = entry()
    c.VALIDATION.unlink(missing_ok=True)
    with c.LOCK.open('a') as held:
        fcntl.flock(held, fcntl.LOCK_EX)
        c.validate(p)
        assert c.generation() == 3 and not c.VALIDATION.exists()
    c.invalidate()
    new_generation = c.generation()
    c.validate(p)
    assert c.generation() == new_generation, 'obsolete validators must not invalidate a newer generation'
print('replacement, deletion, addition, editable-proof exclusion, flock dedup, and obsolete-validator checks passed')
