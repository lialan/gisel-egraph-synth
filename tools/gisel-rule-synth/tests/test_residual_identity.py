"""Search identities retain the SSA boundary while ignoring producer names."""

import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from girs import residual


def value(reg, **extra):
    return dict(reg=reg, w=32, type='s32', zero='0x0', one='0x0',
                noundef=True, **extra)


def tree(fn='f'):
    return {
        'fn': fn, 'bb': 5, 'root': '%12', 'interior': 1,
        'inputs': [value('%9', **{'def': 'COPY'}),
                   value('%10', **{'def': 'COPY'})],
        'expr': value('%12', op='G_ADD', bb=5, uses=2, flags=[],
                      args=[{'in': 0}, {'in': 1}]),
    }


def joint(fn='f'):
    return {
        'kind': 'region', 'fn': fn, 'bb': 5, 'chunk': 0,
        'args_noundef': True,
        'inputs': [value('%9', defined=True, pos=-1, uses=2,
                         **{'def': 'COPY'})],
        'instrs': [
            {'op': 'G_ADD', 'pos': 4, 'flags': [],
             'defs': [value('%10', defined=True, uses=2)],
             'args': [{'in': 0}, {'in': 0}]},
            {'op': 'G_SUB', 'pos': 6, 'flags': [],
             'defs': [value('%12', defined=True, uses=1)],
             'args': [{'node': 0, 'res': 0}, {'in': 0}]},
        ],
    }


def rename(x):
    if isinstance(x, list):
        return [rename(v) for v in x]
    if not isinstance(x, dict):
        return x
    out = {}
    for k, v in reversed(list(x.items())):
        if k in ('reg', 'mi', 'root'):
            out[k] = '%' + str(300 - int(v[1:]))
        elif k == 'fn':
            out[k] = 'renamed_' + v
        elif k == 'bb':
            out[k] = v + 20
        elif k == 'straight_line':
            out[k] = [n + 20 for n in v]
        else:
            out[k] = rename(v)
    return out


class ResidualIdentityTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.serial = 0

    def write(self, records):
        self.serial += 1
        p = self.root / ('source-%d.jsonl' % self.serial)
        p.write_text(''.join(json.dumps(r) + '\n' for r in records))
        return p

    def identity(self, records):
        return residual.fingerprint(self.write(records))

    def test_alpha_renaming_and_json_key_order(self):
        for record in (tree(), joint()):
            with self.subTest(kind=record.get('kind', 'tree')):
                self.assertEqual(self.identity([record]),
                                 self.identity([rename(record)]))
                self.assertEqual(self.identity([record])['conservative_files'], 0)

    def test_tree_context_changes_invalidate(self):
        original = tree()
        mutations = [
            ('type', lambda r: r['expr'].update(type='f32')),
            ('flags', lambda r: r['expr'].update(flags=['nuw'])),
            ('known bits', lambda r: r['inputs'][0].update(zero='0xff')),
            ('definedness', lambda r: r['inputs'][0].update(noundef=False)),
            ('external uses', lambda r: r['expr'].update(uses=3)),
            ('constant', lambda r: r['inputs'][0].update(const='0x1')),
            ('load hint', lambda r: r['expr'].update(load=True, imm=8)),
            ('stage', lambda r: r.update(stage='post-legalizer')),
            ('features', lambda r: r.update(features='+wavefrontsize32')),
            ('fp facts', lambda r: r['inputs'][0].update(
                fp_facts={'classes': 3, 'integral': True})),
        ]
        before = self.identity([original])['sha256']
        for name, mutate in mutations:
            with self.subTest(context=name):
                changed = copy.deepcopy(original)
                mutate(changed)
                self.assertNotEqual(before, self.identity([changed])['sha256'])

    def test_cross_record_sharing_is_function_wide(self):
        first, second = tree(), tree()
        second['root'] = second['expr']['reg'] = '%15'
        second['expr']['op'] = 'G_XOR'
        rows = [first, second]
        self.assertEqual(self.identity(rows), self.identity(rename(rows)))
        changed = copy.deepcopy(rows)
        changed[1]['inputs'][0]['reg'] = '%99'
        self.assertNotEqual(self.identity(rows), self.identity(changed))
        changed = copy.deepcopy(rows)
        changed[1]['fn'] = 'other_function'
        self.assertNotEqual(self.identity(rows), self.identity(changed))

    def test_blocks_and_straight_line_relationships(self):
        rows = [tree(), tree()]
        rows[1]['bb'] = rows[1]['expr']['bb'] = 8
        for r in rows:
            r['straight_line'] = [5, 8]
        self.assertEqual(self.identity(rows), self.identity(rename(rows)))
        changed = copy.deepcopy(rows)
        changed[1]['straight_line'] = [8, 5]
        self.assertNotEqual(self.identity(rows), self.identity(changed))
        changed = copy.deepcopy(rows)
        changed[1]['expr']['bb'] = 5
        self.assertNotEqual(self.identity(rows), self.identity(changed))

    def test_shared_instruction_multi_result_identity(self):
        rows = [tree(), tree()]
        for n, r in enumerate(rows):
            r['root'] = r['expr']['reg'] = '%' + str(12 + n)
            r['expr'].update(op='G_UADDO', mi='%12', res=n)
        self.assertEqual(self.identity(rows), self.identity(rename(rows)))
        changed = copy.deepcopy(rows)
        changed[1]['expr']['mi'] = '%13'
        self.assertNotEqual(self.identity(rows), self.identity(changed))

    def test_joint_context_and_outputs_are_preserved(self):
        original = joint()
        mutations = [
            ('output uses', lambda r: r['instrs'][0]['defs'][0].update(uses=1)),
            ('input users', lambda r: r['inputs'][0].update(uses=17)),
            ('known bits', lambda r: r['instrs'][0]['defs'][0].update(one='0x1')),
            ('definedness', lambda r: r['inputs'][0].update(defined=False)),
            ('noundef', lambda r: r['inputs'][0].update(noundef=False)),
            ('type', lambda r: r['instrs'][0]['defs'][0].update(type='i32')),
            ('flags', lambda r: r['instrs'][0].update(flags=['nsw'])),
            ('position', lambda r: r['instrs'][0].update(pos=5)),
            ('sharing', lambda r: r['instrs'][1]['args'].__setitem__(0, {'in': 0})),
            ('chunk', lambda r: r.update(chunk=1)),
        ]
        before = self.identity([original])['sha256']
        for name, mutate in mutations:
            with self.subTest(context=name):
                changed = copy.deepcopy(original)
                mutate(changed)
                self.assertNotEqual(before, self.identity([changed])['sha256'])

    def test_unknown_bank_memory_and_old_schema_are_conservative(self):
        records = [tree(), joint(), tree()]
        records[0]['inputs'][0]['bank'] = 'SGPR'
        records[1]['instrs'][0]['memory'] = {'volatile': True, 'address_space': 1}
        del records[2]['expr']['type']
        for record in records:
            with self.subTest(record=record):
                before = self.identity([record])
                self.assertEqual(before['conservative_files'], 1)
                self.assertNotEqual(before, self.identity([rename(record)]))
        changed = copy.deepcopy(records[0])
        changed['inputs'][0]['bank'] = 'VGPR'
        self.assertNotEqual(self.identity([records[0]]), self.identity([changed]))

    def test_unknown_export_uses_full_content(self):
        record = {'version': 4, 'fn': 'f', 'stage': 'post-legalizer',
                  'inputs': [], 'original': [], 'optimized': [],
                  'producer': 'old-compiler'}
        old = self.identity([record])
        self.assertEqual(old['conservative_files'], 1)
        record['producer'] = 'new-compiler'
        self.assertNotEqual(old, self.identity([record]))

    def test_file_order_names_and_function_names_do_not_matter(self):
        a, b = self.write([tree('a')]), self.write([joint('b')])
        a2, b2 = self.write([rename(tree('a'))]), self.write([rename(joint('b'))])
        self.assertEqual(residual.fingerprint([a, b]), residual.fingerprint([b2, a2]))
        self.assertNotEqual(residual.fingerprint([a, b]), residual.fingerprint([a, a, b]))
        self.assertEqual(self.identity([tree('a'), joint('b')])['conservative_files'], 1)

    def test_function_grouping_and_record_order_are_preserved(self):
        rows = [tree('a'), tree('b')]
        rows[1]['expr']['op'] = 'G_XOR'
        self.assertEqual(self.identity(rows), self.identity(list(reversed(rows))))
        rows[1]['fn'] = 'a'
        self.assertNotEqual(self.identity(rows), self.identity(list(reversed(rows))))

    def test_malformed_or_duplicate_json_keys_do_not_become_empty(self):
        a = self.root / 'invalid.jsonl'
        a.write_bytes(b'{"fn":"a","fn":"b"}\n')
        self.assertEqual(residual.fingerprint_file(a)['mode'], 'raw')
        before = residual.fingerprint(a)
        a.write_bytes(b'\xffnot json\n')
        self.assertEqual(residual.fingerprint_file(a)['mode'], 'raw')
        self.assertNotEqual(before, residual.fingerprint(a))
        a.write_bytes(b'')
        self.assertEqual(residual.fingerprint_file(a)['mode'], 'empty')
        self.assertNotEqual(before, residual.fingerprint(a))
        with self.assertRaises(OSError):
            residual.fingerprint(self.root / 'missing')


if __name__ == '__main__':
    unittest.main()
