"""Local reusable proof obligations. Never store UNKNOWN as a conclusion."""

import json
import os
import sqlite3
import z3

from . import known


class Proofs:
    def __init__(self, directory, namespace):
        os.makedirs(directory, exist_ok=True)
        self.db = sqlite3.connect(os.path.join(directory, 'proofs.sqlite3'),
                                  timeout=30)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('CREATE TABLE IF NOT EXISTS proofs '
                        '(key TEXT PRIMARY KEY, result TEXT NOT NULL)')
        self.namespace = namespace
        self.hits = self.stored = 0

    def key(self, formula, model):
        # sexpr() alone omits declarations: identical symbol names with
        # different sorts are different obligations. A fresh context also
        # makes SMT-LIB let numbering independent of preceding queries.
        ctx = z3.Context()
        solver = z3.Solver(ctx=ctx)
        solver.add(formula.translate(ctx))
        return known.digest([self.namespace, solver.to_smt2(),
                             None if model is None else
                             [(v.sexpr(), v.sort().sexpr()) for v in model]])

    def get(self, key):
        from .smt import Result
        row = self.db.execute('SELECT result FROM proofs WHERE key=?',
                              (key,)).fetchone()
        if row is None:
            return None
        self.hits += 1
        return Result(**json.loads(row[0]))

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
