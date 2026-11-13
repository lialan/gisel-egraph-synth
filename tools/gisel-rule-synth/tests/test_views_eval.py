#!/usr/bin/env python3
"""Tests of the evaluation drivers of the e-graph features
(eval/views_eval.py, eval/views_diff.py) and of the location of the LLVM
sources (girs/paths.py). No compilation: the parsers are fed fixed text.

Run:  python3 -m unittest discover -s tools/gisel-rule-synth/tests
"""

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)
sys.path.insert(0, os.path.join(ROOT, 'eval'))

import views_diff  # noqa: E402
import views_eval  # noqa: E402

# Trimmed -time-passes output of llc with the pass at both positions.
TIME_PASSES = """\
===-------------------------------------------------------------------------===
                          GlobalISel e-graph combiner
===-------------------------------------------------------------------------===
  Total Execution Time: 0.0356 seconds (0.0357 wall clock)

   ---User Time---   --System Time--   --User+System--   ---Wall Time---  --- Name ---
   0.0210 ( 68.9%)   0.0041 ( 78.1%)   0.0250 ( 70.2%)   0.0250 ( 70.3%)  Saturate e-graph
   0.0062 ( 20.5%)   0.0007 ( 13.6%)   0.0069 ( 19.5%)   0.0069 ( 19.5%)  Extract and rewrite
   0.0032 ( 10.6%)   0.0004 (  8.3%)   0.0037 ( 10.3%)   0.0037 ( 10.3%)  Build e-graph
   0.0304 (100.0%)   0.0052 (100.0%)   0.0356 (100.0%)   0.0357 (100.0%)  Total

===-------------------------------------------------------------------------===
                          Pass execution timing report
===-------------------------------------------------------------------------===
  Total Execution Time: 0.1728 seconds (0.1729 wall clock)

   ---User Time---   --System Time--   --User+System--   ---Wall Time---  --- Name ---
   0.0241 ( 17.2%)   0.0023 (  7.0%)   0.0263 ( 15.2%)   0.0263 ( 15.2%)  GIEGraphCombiner #2
   0.0122 (  8.7%)   0.0032 (  9.9%)   0.0155 (  8.9%)   0.0155 (  8.9%)  GIEGraphCombiner
   0.0043 (  3.0%)   0.0006 (  1.7%)   0.0048 (  2.8%)   0.0048 (  2.8%)  AMDGPUPostLegalizerCombiner
   0.1402 (100.0%)   0.0326 (100.0%)   0.1728 (100.0%)   0.1729 (100.0%)  Total

===-------------------------------------------------------------------------===
                      GlobalISel e-graph combiner analyses
===-------------------------------------------------------------------------===
  Total Execution Time: 0.0007 seconds (0.0007 wall clock)

   ---Wall Time---  --- Name ---
   0.0007 (100.0%)  Uniformity analysis
   0.0007 (100.0%)  Total
"""


class ConfigTest(unittest.TestCase):
    def test_named_configurations(self):
        self.assertEqual(views_eval.flags_of('stock'), [])
        self.assertEqual(views_eval.flags_of('all'), views_eval.EGRAPH)
        self.assertEqual(views_eval.flags_of('no-slice')[-1],
                         '-gisel-egraph-features=all,no-slice')

    def test_feature_sets(self):
        self.assertEqual(views_eval.flags_of('f:facts+patterns+dag')[-1],
                         '-gisel-egraph-features=none,facts,patterns,dag')
        self.assertEqual(views_eval.flags_of('f:')[-1],
                         '-gisel-egraph-features=none')
        with self.assertRaises(SystemExit):
            views_eval.flags_of('f:facts+nosuch')

    def test_defines(self):
        d = views_eval.parse_defines(['x=no-dag -foo=1 "-bar=a b"'])
        self.assertEqual(d, {'x': ('no-dag', ['-foo=1', '-bar=a b'])})
        self.assertEqual(views_eval.flags_of('x', d),
                         views_eval.flags_of('no-dag') + ['-foo=1',
                                                          '-bar=a b'])
        for bad in ('x', 'x=', 'x=nosuch -foo'):
            with self.assertRaises(SystemExit):
                views_eval.parse_defines([bad])


class TimerTest(unittest.TestCase):
    def test_parse(self):
        t = views_eval.parse_timers(TIME_PASSES)
        # User + system where there is such a column, else wall time.
        self.assertAlmostEqual(t['Saturate e-graph'], 0.0250)
        self.assertAlmostEqual(t['Build e-graph'], 0.0037)
        self.assertAlmostEqual(t['Extract and rewrite'], 0.0069)
        self.assertAlmostEqual(t['Uniformity analysis'], 0.0007)
        # Both instances of the pass; no other pass and no total.
        self.assertAlmostEqual(t['pass'], 0.0263 + 0.0155)
        self.assertEqual(sorted(t), ['Build e-graph', 'Extract and rewrite',
                                     'Saturate e-graph',
                                     'Uniformity analysis', 'pass'])

    def test_no_timers(self):
        self.assertEqual(views_eval.parse_timers('warning: x\n'), {})


def result(insns, rc=0, fallback=(), **mn):
    return {'rc': rc, 'insns': insns, 'code_bytes': 4 * insns, 'sgpr': 1,
            'vgpr': 1, 'fallback': list(fallback), 'mnemonics': mn}


class DiffTest(unittest.TestCase):
    def write(self, d, files):
        path = os.path.join(d, '%d.json' % len(os.listdir(d)))
        with open(path, 'w') as f:
            json.dump({'files': files}, f)
        return path

    def test_compare(self):
        with tempfile.TemporaryDirectory() as d:
            run = self.write(d, {
                'a.ll': {'none': result(10, v_mov_b32=2),
                         'all': result(8, v_mov_b32=1)},
                'b.ll': {'none': result(5), 'all': result(6)},
                'c.ll': {'none': result(5), 'all': result(5)},
                # Not comparable: one configuration fails.
                'd.ll': {'none': result(5), 'all': result(0, rc=1)},
                # Not comparable: different fallbacks.
                'e.ll': {'none': result(5, fallback=['f']),
                         'all': result(5)}})
            c = views_diff.compare(views_diff.load(run + ':none'),
                                   views_diff.load(run))
            self.assertEqual(c['files'], ['a.ll', 'b.ll', 'c.ll'])
            self.assertEqual(c['delta']['a.ll'], (-2, -8, -2))
            self.assertEqual((c['better'], c['worse']), (1, 1))
            self.assertEqual(c['totals']['b']['insns'] -
                             c['totals']['a']['insns'], -1)
            self.assertEqual(c['mnemonics']['b']['v_mov_b32'] -
                             c['mnemonics']['a']['v_mov_b32'], -1)
            # Pairwise: d.ll still fails in `all`; e.ll differs in
            # fallbacks between the two configurations compared.
            p = views_diff.compare(views_diff.load(run + ':none'),
                                   views_diff.load(run + ':all'),
                                   pairwise=True)
            self.assertEqual(p['files'], ['a.ll', 'b.ll', 'c.ll'])
            # A file that only fails in another configuration of a run is
            # left out by default, kept with --pairwise.
            run2 = self.write(d, {
                'a.ll': {'stock': result(9), 'none': result(9),
                         'all': result(9)},
                'b.ll': {'stock': result(0, rc=1), 'none': result(5),
                         'all': result(5)}})
            c = views_diff.compare(views_diff.load(run2 + ':none'),
                                   views_diff.load(run2 + ':all'))
            self.assertEqual(c['files'], ['a.ll'])
            p = views_diff.compare(views_diff.load(run2 + ':none'),
                                   views_diff.load(run2 + ':all'),
                                   pairwise=True)
            self.assertEqual(p['files'], ['a.ll', 'b.ll'])


class HintsTest(unittest.TestCase):
    def test_hints_apart(self):
        # The same selected code with one more s_delay_alu: worse in
        # instructions, equal without the hints.
        with tempfile.TemporaryDirectory() as d:
            a, b = result(10), result(11)
            a['hints'], b['hints'] = 2, 3
            path = os.path.join(d, 'r.json')
            with open(path, 'w') as f:
                json.dump({'files': {'x.ll': {'none': a, 'all': b}}}, f)
            c = views_diff.compare(views_diff.load(path + ':none'),
                                   views_diff.load(path))
            self.assertEqual(c['delta']['x.ll'], (1, 4, 0))
            self.assertEqual((c['worse'], c['real_worse']), (1, 0))

    def test_hint_mnemonics(self):
        self.assertIn('s_delay_alu', views_eval.HINTS)
        self.assertNotIn('v_mov_b32', views_eval.HINTS)


class LLVMRootTest(unittest.TestCase):
    def root(self, env):
        env = dict(os.environ, **env)
        return subprocess.run(
            [sys.executable, '-c', 'from girs import paths; '
             'print(paths.LLVM_ROOT)'], cwd=ROOT, env=env, check=True,
            capture_output=True, text=True).stdout.strip()

    def test_override(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertEqual(self.root({'GIRS_LLVM_ROOT': d}), d)

    def test_from_the_llvm_build(self):
        # A build directory configured from SRC/llvm names SRC, if the
        # repository's own submodule is not checked out.
        with tempfile.TemporaryDirectory() as d:
            src = os.path.join(d, 'src')
            os.makedirs(os.path.join(src, 'llvm'))
            build = os.path.join(d, 'build')
            os.makedirs(build)
            with open(os.path.join(build, 'CMakeCache.txt'), 'w') as f:
                f.write('LLVM_SOURCE_DIR:STATIC=%s\n' %
                        os.path.join(src, 'llvm'))
            env = {'GIRS_LLVM_BUILD': build, 'GIRS_LLVM_ROOT': ''}
            own = os.path.join(os.path.dirname(os.path.dirname(ROOT)),
                               'third_party', 'llvm-project')
            expected = own if os.path.isdir(os.path.join(own, 'llvm')) \
                else src
            self.assertEqual(self.root(env), expected)


if __name__ == '__main__':
    unittest.main()
