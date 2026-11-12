"""Tests of the per-file results that mine keeps for an interrupted stage
(Run._compile_many)."""

import json
import os
import sys
import tempfile
import types
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(
    __file__))))

from girs import measure, mine  # noqa: E402


class CompileManyResumeTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.calls = []
        self.llc = self.file('llc', 'compiler 1')
        self.src = [self.file('a.ll', 'a'), self.file('b.ll', 'b')]
        self.out = os.path.join(self.dir, 'final.json')
        self.run = types.SimpleNamespace(
            cfg={'jobs': 2}, target=types.SimpleNamespace(name='AMDGPU'))
        self.run._compile_identity = types.MethodType(
            mine.Run._compile_identity, self.run)

    def file(self, name, text):
        path = os.path.join(self.dir, name)
        with open(path, 'w') as f:
            f.write(text)
        return path

    def compile(self, **kw):
        def fake(llc, target, path, flags=(), synth=False, disabled=(),
                 count_rules=True):
            self.calls.append(path)
            return {'rc': 0, 'insns': len(self.calls)}
        with mock.patch.object(measure, 'compile_ll', fake):
            return mine.Run._compile_many(self.run, self.llc, self.src,
                                          self.out, **kw)

    def interrupt(self, **kw):
        """Leaves the .part file of a stage that compiled a.ll only."""
        res = self.compile(**kw)
        ident = mine.Run._compile_identity(
            self.run, self.llc, kw.get('synth', False),
            kw.get('disabled', ()), kw.get('flags', ()), True)
        with open(self.out + '.part', 'w') as f:
            f.write(json.dumps({'identity': ident}) + '\n')
            f.write(json.dumps([self.src[0], mine._sha_content(self.src[0]),
                                {'rc': 0, 'insns': 10}]) + '\n')
        self.calls.clear()
        return res

    def test_same_identity_continues(self):
        self.interrupt(disabled=('r1',))
        res = self.compile(disabled=('r1',))
        self.assertEqual(self.calls, [self.src[1]])
        self.assertEqual(res[self.src[0]]['insns'], 10)

    def test_other_rules_or_flags_compile_again(self):
        for kw in ({'disabled': ('r2',)}, {'flags': ('-O3',)},
                   {'synth': True}):
            with self.subTest(**kw):
                self.interrupt(disabled=('r1',))
                res = self.compile(**kw)
                self.assertEqual(sorted(self.calls), sorted(self.src))
                self.assertNotEqual(res[self.src[0]]['insns'], 10)

    def test_other_compiler_compiles_again(self):
        self.interrupt()
        self.file('llc', 'compiler 2')
        self.compile()
        self.assertEqual(sorted(self.calls), sorted(self.src))

    def test_changed_file_compiles_again(self):
        self.interrupt()
        self.file('a.ll', 'a changed')
        self.compile()
        self.assertEqual(sorted(self.calls), sorted(self.src))

    def test_old_format_compiles_again(self):
        with open(self.out + '.part', 'w') as f:
            f.write(json.dumps([self.src[0], {'rc': 0, 'insns': 10}]) +
                    '\n')
        res = self.compile()
        self.assertEqual(sorted(self.calls), sorted(self.src))
        self.assertNotEqual(res[self.src[0]]['insns'], 10)


class CacheIdentityTest(unittest.TestCase):
    def test_model_hash_has_every_module(self):
        import importlib.util
        here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        spec = importlib.util.spec_from_file_location(
            'cli', os.path.join(here, 'gi-rule-synth.py'))
        cli = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cli)
        seen = []
        with mock.patch.object(cli, '_sha', lambda files: seen.extend(files)):
            cli._model_sha()
        names = {os.path.basename(f) for f in seen}
        for name in ('amdgcn.py', 'vector.py', 'synth.py', 'smt.py',
                     'gmir_ops.json'):
            self.assertIn(name, names)

    def test_instance_key_has_the_kinds(self):
        from girs import corpus
        e = ('G_SELECT', 32, ('var', 0), ('var', 1), ('var', 2))
        facts = ((0, 0), (0, 0), (0, 0))
        f = corpus.Instance(e, (1, 32, 32), facts, (None,) * 3, (), (), [],
                            kinds=('i', 'f', 'f'))
        i = corpus.Instance(e, (1, 32, 32), facts, (None,) * 3, (), (), [],
                            kinds=('i', 'i', 'i'))
        self.assertNotEqual(f.vk, i.vk)
        self.assertNotEqual(f.key(), i.key())


if __name__ == '__main__':
    unittest.main()
