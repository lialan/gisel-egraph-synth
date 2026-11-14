"""Exact solver results survive compiler contract changes, rules do not."""

import contextlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from girs import history, joint, joint_tasks, known, smt
import z3


@contextlib.contextmanager
def backend(directory, namespace=None, timeout_ms=1000):
    value = smt.Z3Backend(timeout_ms=timeout_ms)
    value.history = history.Proofs(directory, namespace)
    try:
        yield value
    finally:
        value.history.close()


@contextlib.contextmanager
def edited_source(suffix):
    """Change the bytes used by identity hashing without editing the checkout."""
    original = Path.read_bytes

    def read(path):
        data = original(path)
        return data + b'\n# changed implementation\n' if str(path).endswith(suffix) else data

    with mock.patch.object(Path, 'read_bytes', read):
        yield


class ProofCacheIdentityTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = self.tmp.name
        self.x = z3.BitVec('x', 8)
        self.formula = self.x != self.x

    def seed(self, namespace=None):
        with backend(self.directory, namespace) as b:
            self.assertEqual(b.check(self.formula).status, 'unsat')
            self.assertEqual(b.check(self.x == 7, [self.x]).model, [7])

    def assert_reused(self):
        with backend(self.directory, timeout_ms=10000) as b, \
                mock.patch.object(b, '_check', side_effect=AssertionError('cached obligation')):
            self.assertEqual(b.check(self.formula).status, 'unsat')
            self.assertEqual(b.check(self.x == 7, [self.x]).model, [7])
            self.assertEqual(b.history.hits, 2)
            self.assertEqual(b.calls, 0)

    def test_runtime_contract_changes_reuse_proofs_but_reject_catalog(self):
        self.seed()
        catalog = known.stamp({'rules': []})
        namespace = known.proof_namespace()
        for source in ('girs/emit.py', 'girs/match.py', 'girs/corpus.py',
                       'lib/GISynthCorpusExtractor.cpp', 'lib/SynthCombiner.inc'):
            with self.subTest(source=source), edited_source(source):
                self.assertEqual(known.proof_namespace(), namespace)
                with self.assertRaisesRegex(ValueError, 'revalidation'):
                    known.require_current(catalog)
                self.assert_reused()

    def test_search_changes_keep_decisions_and_catalog(self):
        self.seed()
        catalog = known.stamp({'rules': []})
        search = known.search_sha()
        namespace = known.proof_namespace()
        for source in ('girs/discover.py', 'girs/parallel.py', 'girs/views.py'):
            with self.subTest(source=source), edited_source(source):
                self.assertNotEqual(known.search_sha(), search)
                self.assertEqual(known.proof_namespace(), namespace)
                known.require_current(catalog)
                self.assert_reused()

    def test_model_source_edit_still_requires_current_obligation(self):
        self.seed()
        catalog = known.stamp({'rules': []})
        with edited_source('girs/smt.py'):
            with self.assertRaisesRegex(ValueError, 'revalidation'):
                known.require_current(catalog)
            # The source fingerprint does not revoke a mathematical fact.
            self.assert_reused()
            # Corrected assumptions change the actual query, which is solved.
            with backend(self.directory) as b:
                self.assertEqual(b.check(self.x == 8, [self.x]).model, [8])
                self.assertEqual(b.calls, 1)
                self.assertEqual(b.history.hits, 0)

    def test_trust_epoch_revokes_history_and_catalog_together(self):
        self.seed()
        catalog = known.stamp({'rules': []})
        namespace = known.proof_namespace()
        for epoch in ('PROOF_MODEL_EPOCH', 'PROOF_SOLVER_EPOCH'):
            with self.subTest(epoch=epoch), \
                    mock.patch.object(known, epoch, getattr(known, epoch) + 1):
                self.assertNotEqual(known.proof_namespace(), namespace)
                with self.assertRaisesRegex(ValueError, 'revalidation'):
                    known.require_current(catalog)
                with backend(self.directory) as b:
                    self.assertEqual(b.check(self.formula).status, 'unsat')
                    self.assertEqual(b.calls, 1)
                    self.assertEqual(b.history.hits, 0)

    def test_cache_format_change_does_not_revoke_catalog_contract(self):
        self.seed()
        catalog = known.stamp({'rules': []})
        with mock.patch.object(known, 'PROOF_CACHE_SCHEMA', known.PROOF_CACHE_SCHEMA + 1):
            known.require_current(catalog)
            with backend(self.directory) as b:
                self.assertIsNone(b.history.get(b.history.key(self.formula, None)))

    def test_legacy_namespace_is_preserved_but_not_implicitly_promoted(self):
        legacy = known.semantics_sha()
        self.seed(legacy)
        with backend(self.directory) as b:
            self.assertIsNone(b.history.get(b.history.key(self.formula, None)))
            self.assertEqual(b.check(self.formula).status, 'unsat')
            self.assertEqual(b.calls, 1)
        with backend(self.directory, legacy) as b, \
                mock.patch.object(b, '_check', side_effect=AssertionError('legacy proof')):
            self.assertEqual(b.check(self.formula).status, 'unsat')
            self.assertEqual(b.check(self.x == 7, [self.x]).model, [7])

    def test_query_widths_and_assumptions_do_not_alias(self):
        one = z3.BitVec('same_name', 1)
        two = z3.BitVec('same_name', 2)
        with backend(self.directory) as b:
            self.assertEqual((-one != one).sexpr(), (-two != two).sexpr())
            self.assertEqual(b.check(-one != one).status, 'unsat')
            self.assertEqual(b.check(-two != two).status, 'sat')
            self.assertEqual(b.check(z3.And(self.x == 0, self.x != 0)).status, 'unsat')
            self.assertEqual(b.check(z3.And(self.x == 1, self.x != 0)).status, 'sat')
            self.assertEqual(b.calls, 4)

    def test_model_projection_declarations_and_order_are_in_the_key(self):
        y = z3.BitVec('y', 8)
        with backend(self.directory) as b:
            formula = z3.And(self.x == 3, y == 5)
            self.assertEqual(b.check(formula, [self.x, y]).model, [3, 5])
            self.assertEqual(b.check(formula, [y, self.x]).model, [5, 3])
            self.assertEqual(b.calls, 2)
            # Same term text and output sort, different argument declarations.
            # These declarations do not occur in the formula itself.
            a = z3.BitVec('arg', 8)
            c = z3.BitVec('arg', 16)
            f = z3.Function('projection', a.sort(), self.x.sort())
            g = z3.Function('projection', c.sort(), self.x.sort())
            self.assertEqual(f(a).sexpr(), g(c).sexpr())
            self.assertEqual(f(a).sort(), g(c).sort())
            self.assertNotEqual(b.history.key(z3.BoolVal(True), [f(a)]),
                                b.history.key(z3.BoolVal(True), [g(c)]))

    def test_unknown_attempt_is_retryable_and_not_a_persistent_conclusion(self):
        with backend(self.directory) as b:
            with mock.patch.object(b, '_check', return_value=smt.Result('unknown')):
                self.assertEqual(b.check(self.formula).status, 'unknown')
            key = b.history.key(self.formula, None)
            self.assertIsNone(b.history.get(key))
            # Also tolerate a legacy/imported attempt without keeping it as a
            # permanent cache hit or preventing a later decided insertion.
            with b.history.db:
                b.history.db.execute('INSERT INTO proofs VALUES (?, ?)',
                                     (key, json.dumps({'status': 'unknown'})))
            self.assertEqual(b.check(self.formula).status, 'unsat')
            with mock.patch.object(b, '_check', side_effect=AssertionError('decided proof')):
                self.assertEqual(b.check(self.formula).status, 'unsat')
            self.assertEqual(b.calls, 1)

    def test_joint_contract_and_proof_history_have_distinct_identities(self):
        self.seed()
        namespace = known.proof_namespace()
        with mock.patch.object(joint_tasks, 'semantics_sha', return_value='changed joint contract'):
            with mock.patch.object(joint_tasks, '_prepare_history',
                                   wraps=joint_tasks._prepare_history) as prepare:
                _, _, stats = joint_tasks.run({}, joint.Limits(), cache=self.directory, jobs=1)
            self.assertEqual(prepare.call_args.args[2], namespace)
            self.assertEqual(stats['semantics_sha'], 'changed joint contract')
            self.assertEqual(stats['proof_namespace'], namespace)
            self.assert_reused()


if __name__ == '__main__':
    unittest.main()
