#!/usr/bin/env python3
"""Exercise cache keys and deliberate absence of filesystem invalidation."""
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('editor_cache', Path(__file__).with_name('editor-setup-cache.py'))
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)


class Buffer:
    def __init__(self, data=b''):
        self.buffer = io.BytesIO(data)


class CacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve() / 'repo/version/playground'
        self.root.mkdir(parents=True)
        self.tc = self.root / '.lake/toolchains/stage2'
        self.cache = self.root / '.lake/editor-setup-cache'
        for d in ['bin', 'lib/lean', 'src']:
            (self.tc / d).mkdir(parents=True)
        self.cache.mkdir()
        (self.root / 'Playground').mkdir()
        self.source = self.root / 'Playground/Test.lean'
        self.source.write_text('import Init\n')
        self.art = self.tc / 'lib/lean/Init.olean'
        self.art.write_bytes(b'original')
        (self.root / 'lakefile.toml').write_text('name = "test"\n')
        self.addCleanup(patch.stopall)
        for name, value in {'PROJECT': self.root, 'SYSROOT': self.tc, 'CACHE': self.cache,
                            'REAL_LAKE': self.tc / 'bin/lake.real'}.items():
            patch.object(c, name, value).start()
        patch.dict(os.environ, {'LEAN_PATH': '', 'LEAN_EDITOR_SETUP_CACHE': '1'}, clear=True).start()
        old = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, old)
        (self.cache / 'configuration.json').write_text(json.dumps({'digest': c.configuration_digest()}))
        self.calls = 0
        self.fail = False
        self.mutate = False
        self.header = {'isModule': False, 'imports': []}
        self.args = ['setup-file', str(self.source), '-', '--no-build', '--no-cache']

    def lake(self, args, input=None, **kwargs):
        self.calls += 1
        if self.mutate:
            self.art.write_bytes(b'changed during setup')
        data = json.dumps({'dynlibs': [], 'plugins': [], 'importArts': {'Init': [[str(self.art)], []]}}).encode()
        return subprocess.CompletedProcess(args, 3 if self.fail else 0, data)

    def run_cache(self):
        output = Buffer()
        with patch.object(sys, 'argv', ['cache', *self.args]), \
             patch.object(sys, 'stdin', Buffer(json.dumps(self.header).encode())), \
             patch.object(sys, 'stdout', output), patch.object(c.subprocess, 'run', self.lake):
            rc = c.main()
        return rc, output.buffer.getvalue()

    def warm(self):
        a = self.run_cache()
        b = self.run_cache()
        self.assertEqual(a, b)
        self.assertEqual(self.calls, 1)

    def test_hit_is_identical(self):
        self.warm()

    def test_proof_body_change_can_reuse_setup(self):
        self.warm()
        self.source.write_text('import Init\n-- changed\n')
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_dependency_source_change(self):
        dep = self.source.with_name('Dependency.lean')
        dep.write_text('import Init\n')
        self.warm()
        dep.write_text('import Init\n-- changed\n')
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_unsaved_header(self):
        self.warm()
        self.header['imports'] = [{'module': 'MissingModule'}]
        self.run_cache()
        self.assertEqual(self.calls, 2)

    def test_artifact_write_preserving_mtime(self):
        self.warm()
        s = self.art.stat()
        self.art.write_bytes(b'modified')
        os.utime(self.art, ns=(s.st_atime_ns, s.st_mtime_ns))
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_add_remove_and_rename(self):
        self.warm()
        path = self.source.with_name('New.lean')
        path.write_text('import Init\n')
        self.run_cache()
        renamed = path.with_name('Renamed.lean')
        path.rename(renamed)
        self.run_cache()
        renamed.unlink()
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_config_change_disables_cache(self):
        self.warm()
        (self.root / 'lakefile.toml').write_text('name = "different"\n')
        self.assertFalse(c.eligible(self.args))

    def test_environment_and_flags(self):
        self.warm()
        os.environ['LEAN_SOME_OPTION'] = 'changed'
        self.run_cache()
        self.args = self.args[:3]
        self.run_cache()
        self.assertEqual(self.calls, 3)

    def test_corrupt_cache(self):
        self.warm()
        for path in self.cache.glob('*.json'):
            if path.name != 'configuration.json':
                path.write_text('{"stdout": null}')
        self.run_cache()
        self.assertEqual(self.calls, 2)

    def test_failed_setup_not_cached(self):
        self.fail = True
        self.assertEqual(self.run_cache()[0], 3)
        self.assertEqual(self.run_cache()[0], 3)
        self.assertEqual(self.calls, 2)

    def test_changes_during_setup_cached(self):
        self.mutate = True
        self.run_cache()
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_external_symlink_does_not_invalidate(self):
        (self.root / 'external').symlink_to(Path(self.temp.name))
        self.run_cache()
        self.run_cache()
        self.assertEqual(self.calls, 1)

    def test_external_search_path_and_custom_flags_bypass(self):
        os.environ['LEAN_PATH'] = '/tmp/external'
        self.assertFalse(c.eligible(self.args))
        os.environ['LEAN_PATH'] = ''
        self.assertFalse(c.eligible(self.args + ['--rehash']))
        self.assertFalse(c.eligible(['build']))


if __name__ == '__main__':
    unittest.main()
