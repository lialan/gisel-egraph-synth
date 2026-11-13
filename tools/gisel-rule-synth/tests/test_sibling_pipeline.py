"""The scalar sibling search must not evaluate whole-vector operations."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
spec = importlib.util.spec_from_file_location("sibling_pipeline_cli",
                                              ROOT / "gi-rule-synth.py")
cli = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cli)


class SiblingPipelineTest(unittest.TestCase):
    def test_vector_sibling_is_reported_and_scalar_pairs_still_search(self):
        inputs = [{"reg": r, "w": 32, "type": "s32", "zero": "0x0",
                   "one": "0x0", "noundef": False, "def": "COPY"}
                  for r in ("%x", "%y")]
        records = []
        for op, w, reg, extra in [
                ("G_SUB", 32, "%d", {}),
                ("G_ICMP", 1, "%c", {"pred": "ult"}),
                ("G_BUILD_VECTOR", 32, "%v",
                 {"lanes": 2, "type": "<2 x s32>"})]:
            expr = {"op": op, "w": w, "type": "s%d" % w, "reg": reg,
                    "zero": "0x0", "one": "0x0", "uses": 1, "flags": [],
                    "args": [{"in": 0}, {"in": 1}], **extra}
            records.append({"fn": "f", "bb": 0, "root": reg, "interior": 1,
                            "expr": expr, "inputs": inputs})
        for cross_block in (False, True):
            if cross_block:
                records = [dict(r, bb=1 if r['root'] == '%c' else 0,
                                straight_line=[0, 1]) for r in records]
            with self.subTest(cross_block=cross_block), \
                    tempfile.TemporaryDirectory() as tmp:
                p = Path(tmp)
                corpus = p / "mixed.jsonl"
                corpus.write_text("".join(json.dumps(r) + "\n" for r in records))
                cli.cmd_synth(cli.default_args(
                    "synth", corpus=[str(corpus)], o=str(p / "rules.json"),
                    stats=str(p / "stats.json"), proofs=str(p / "proofs"),
                    cache="", grammar="registry", regions=True, siblings=True,
                    max_rhs_cost=1, max_evals=100000, max_terms=5000))
                stats = json.loads((p / "stats.json").read_text())
                self.assertEqual(stats["discovery"]["instances"], 3)
                self.assertEqual(stats["discovery"]["vector_instances"], 1)
                self.assertGreater(
                    stats["siblings"]["corpus"]["unsupported_vector_groups"], 0)
                self.assertGreater(stats["siblings"]["rules"], 0)
                if cross_block:
                    self.assertGreater(
                        stats["siblings"]["corpus"]["cross_block_pairs"], 0)

    def test_lifted_root_does_not_hide_vector_or_bad_sibling_types(self):
        inputs = [{"reg": r, "w": 32, "lanes": 2,
                   "type": "<2 x s32>", "zero": "0x0", "one": "0x0",
                   "noundef": False, "def": "COPY"} for r in ("%x", "%y")]
        def record(op, w, reg, args, ins, **extra):
            return {"fn": "lifted", "bb": 0, "root": reg, "interior": 1,
                    "expr": {"op": op, "w": w, "type": "s%d" % w,
                             "reg": reg, "zero": "0x0", "one": "0x0",
                             "uses": 1, "flags": [], "args": args, **extra},
                    "inputs": ins}
        zero = {"reg": "%zero", "w": 32, "type": "s32",
                "zero": "0xffffffff", "one": "0x0", "const": "0x0",
                "noundef": True, "def": "G_CONSTANT"}
        records = [
            record("G_ADD", 32, "%add", [{"in": 0}, {"in": 1}], inputs,
                   lanes=2, type="<2 x s32>"),
            record("G_EXTRACT_VECTOR_ELT", 32, "%lane",
                   [{"in": 0}, {"in": 1}], [inputs[0], zero]),
            record("G_BITCAST", 64, "%bits", [{"in": 0}], [inputs[0]])]
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp)
            corpus = p / "lifted.jsonl"
            corpus.write_text("".join(json.dumps(r) + "\n" for r in records))
            cli.cmd_synth(cli.default_args(
                "synth", corpus=[str(corpus)], o=str(p / "rules.json"),
                stats=str(p / "stats.json"), proofs=str(p / "proofs"),
                cache="", grammar="registry", regions=True, siblings=True,
                max_rhs_cost=1, max_evals=100000, max_terms=5000))
            stats = json.loads((p / "stats.json").read_text())
            self.assertGreater(
                stats["siblings"]["corpus"]["unsupported_vector_groups"], 0)
            self.assertGreater(
                stats["siblings"]["corpus"]["ill_typed_groups"], 0)


if __name__ == "__main__":
    unittest.main()
