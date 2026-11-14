"""Local exact SMT obligations, independent of runtime rule contracts.

A hit certifies the encoded formula only. It does not validate the extractor,
matcher, emitter, target legality or profitability of a rule. Catalogs retain
their stricter identity in known.py. Never store UNKNOWN as a conclusion.
"""

import json
import os
import sqlite3
import z3

from . import known


class Proofs:
    def __init__(self, directory, namespace=None):
        os.makedirs(directory, exist_ok=True)
        self.db = sqlite3.connect(os.path.join(directory, 'proofs.sqlite3'),
                                  timeout=30)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('CREATE TABLE IF NOT EXISTS proofs '
                        '(key TEXT PRIMARY KEY, result TEXT NOT NULL)')
        # Explicit namespaces remain supported for callers with a separate
        # trust domain. Legacy catalog-keyed rows are kept, not silently
        # imported into the new exact-obligation namespace.
        self.namespace = known.proof_namespace() if namespace is None else namespace
        self.hits = self.stored = 0

    def key(self, formula, model):
        # sexpr() alone omits declarations: identical symbol names with
        # different sorts are different obligations. A fresh context also
        # makes SMT-LIB let numbering independent of preceding queries.
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        solver.add(formula.translate(ctx))
        if model is not None:
            # Model projections can mention declarations absent from formula.
            # Their result sort alone does not describe a function's argument
            # sorts. Reflexive equalities retain the complete declarations in
            # the serialized key without changing satisfiability.
            for value in model:
                value = value.translate(ctx)
                solver.add(value == value)
        return known.digest([self.namespace, solver.to_smt2(),
                             None if model is None else
                             [(v.sexpr(), v.sort().sexpr()) for v in model]])

    def get(self, key):
        from .smt import Result
        row = self.db.execute('SELECT result FROM proofs WHERE key=?',
                              (key,)).fetchone()
        if row is None:
            return None
        value = json.loads(row[0])
        if value.get('status') not in ('sat', 'unsat'):
            # An old or externally populated cache may contain an attempt.
            # Remove only the row we read, so a later decided result can be
            # inserted and a concurrent replacement is not discarded.
            with self.db:
                self.db.execute('DELETE FROM proofs WHERE key=? AND result=?',
                                (key, row[0]))
            return None
        self.hits += 1
        return Result(**value)

    def put(self, key, result):
        if result.status not in ('sat', 'unsat'):
            return
        value = {k: getattr(result, k) for k in
                 ('status', 'model', 'smt2', 'timeout_ms')}
        with self.db:
            self.db.execute('INSERT OR IGNORE INTO proofs VALUES (?, ?)',
                            (key, json.dumps(value)))
        self.stored += 1

    def close(self):
        self.db.close()
