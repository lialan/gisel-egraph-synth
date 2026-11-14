"""Content identities of extracted residuals, independent of their producer.

This is an identity for reusing *search*, not an applicability certificate or a
code-generation/measurement cache key. Callers must also key the search model,
legality, target, baseline and limits, and recheck candidates with the current
compiler. Source provenance is maintained separately by the caller.

The current tree and joint extractors write a JSON SSA representation. Keep all
its fields (not Instance.key()/joint.canonical(), which intentionally omit some
context), and alpha-rename only its documented function, block and register
identifiers. Register identity is function-wide across records: normalizing
each tree separately would lose the sharing used by sibling/region search.
Instruction/operand order, chunking, facts, LLTs, flags, use counts and boundary
information all remain. We do not parse MIR or infer missing context.

Unknown/older schemas, including e-graph exports, use the complete file bytes.
In particular, new memory or bank fields must not silently disappear. Such a
file can still be reused byte-for-byte, but gets no alpha-renaming relaxation.
"""

import hashlib
import json
import os
import re


SCHEMA = 'gisel-residual-identity/1'
_VREG = re.compile(r'%[0-9]+\Z')


class _Conservative(ValueError):
    pass


def _object(value, required, optional=()):
    if not isinstance(value, dict) or not set(required) <= value.keys() or \
            value.keys() - set(required) - set(optional):
        raise _Conservative('unrecognized record fields')


def _integer(value):
    if type(value) is not int or value < 0:
        raise _Conservative('unrecognized identifier')


def _reg(value):
    # The two current extractors write numbered virtual registers only.
    if not isinstance(value, str) or not _VREG.fullmatch(value):
        raise _Conservative('unrecognized register')


def _list(value):
    if not isinstance(value, list):
        raise _Conservative('expected an array')
    return value


def _facts(value):
    if 'fp_facts' in value:
        _object(value['fp_facts'], ('classes', 'integral'), ('lower', 'upper'))


_VALUE = ('reg', 'w', 'type', 'zero', 'one', 'noundef')
_CONTEXT = ('stage', 'triple', 'cpu', 'features')


def _tree_node(node, inputs):
    if isinstance(node, dict) and 'in' in node:
        _object(node, ('in',))
        _integer(node['in'])
        if node['in'] >= inputs:
            raise _Conservative('unknown tree input')
        return
    _object(node, _VALUE + ('op', 'bb', 'uses', 'flags', 'args'),
            ('lanes', 'fp_facts', 'pred', 'imm', 'mask', 'res', 'mi', 'load'))
    _reg(node['reg'])
    _integer(node['bb'])
    if 'mi' in node:
        _reg(node['mi'])
    _facts(node)
    for arg in _list(node['args']):
        _tree_node(arg, inputs)


def _tree(rec):
    _object(rec, ('fn', 'bb', 'root', 'interior', 'expr', 'inputs'),
            ('straight_line',) + _CONTEXT)
    _reg(rec['root'])
    for bb in _list(rec.get('straight_line', [])):
        _integer(bb)
    for inp in _list(rec['inputs']):
        _object(inp, _VALUE + ('def',), ('lanes', 'fp_facts', 'address', 'const'))
        _reg(inp['reg'])
        _facts(inp)
    _tree_node(rec['expr'], len(rec['inputs']))


def _joint(rec):
    _object(rec, ('kind', 'fn', 'bb', 'chunk', 'args_noundef', 'inputs', 'instrs'),
            _CONTEXT)
    for inp in _list(rec['inputs']):
        _object(inp, _VALUE + ('defined', 'def', 'pos', 'uses'), ('const',))
        _reg(inp['reg'])
    instrs = _list(rec['instrs'])
    for k, ins in enumerate(instrs):
        _object(ins, ('op', 'pos', 'flags', 'defs', 'args'), ('pred', 'imm'))
        for value in _list(ins['defs']):
            _object(value, _VALUE + ('defined', 'uses'))
            _reg(value['reg'])
        for arg in _list(ins['args']):
            if isinstance(arg, dict) and 'in' in arg:
                _object(arg, ('in',))
                _integer(arg['in'])
                if arg['in'] >= len(rec['inputs']):
                    raise _Conservative('unknown region input')
            else:
                _object(arg, ('node', 'res'))
                _integer(arg['node'])
                _integer(arg['res'])
                if arg['node'] >= k or \
                        arg['res'] >= len(instrs[arg['node']]['defs']):
                    raise _Conservative('unknown region result')


def _record(rec):
    if not isinstance(rec, dict) or not isinstance(rec.get('fn'), str):
        raise _Conservative('missing function scope')
    _integer(rec.get('bb'))
    if rec.get('kind') == 'region':
        _joint(rec)
        return 'joint'
    _tree(rec)
    return 'tree'


class _Scope:
    def __init__(self):
        self.regs, self.blocks = {}, {}

    @staticmethod
    def _id(table, value):
        if value not in table:
            table[value] = len(table)
        return table[value]

    def rename(self, value):
        if isinstance(value, list):
            return [self.rename(v) for v in value]
        if not isinstance(value, dict):
            return value
        out = {}
        # JSON object spelling/order must not influence first-occurrence IDs.
        for key in sorted(value):
            item = value[key]
            if key == 'fn':
                continue  # Its grouping is retained by _semantic().
            if key in ('reg', 'mi', 'root'):
                out[key] = self._id(self.regs, item)
            elif key == 'bb':
                out[key] = self._id(self.blocks, item)
            elif key == 'straight_line':
                out[key] = [self._id(self.blocks, bb) for bb in item]
            elif key in ('expr', 'inputs', 'instrs', 'defs', 'args'):
                out[key] = self.rename(item)
            else:
                # Facts/attributes/context are opaque semantic values, not
                # places in which arbitrary similarly named keys are IDs.
                out[key] = item
        return out


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'),
                      ensure_ascii=True, allow_nan=False).encode()


def _digest(value):
    return hashlib.sha256(_json(value)).hexdigest()


def _semantic(records):
    functions, kinds = {}, set()
    for rec in records:
        kinds.add(_record(rec))
        functions.setdefault(rec['fn'], []).append(rec)
    if len(kinds) > 1:
        raise _Conservative('mixed extractor schemas')
    scopes = []
    for rows in functions.values():
        scope = _Scope()
        scopes.append(_digest([scope.rename(rec) for rec in rows]))
    # Functions/files are independent scopes. Preserve their multiplicity,
    # their record order, and their grouping, but not their names or paths.
    return {'kind': next(iter(kinds), 'empty'), 'functions': sorted(scopes)}


def _pairs(items):
    value = {}
    for key, item in items:
        if key in value:
            raise _Conservative('duplicate JSON key')
        value[key] = item
    return value


def _constant(value):
    raise _Conservative('non-finite JSON number')


def fingerprint_file(path):
    """A path-independent identity plus diagnostics for one JSON-lines file.

    Unreadable files raise OSError; malformed/unknown files are hashed in full,
    never mistaken for an empty corpus. No producer revision is consulted.
    """
    with open(path, 'rb') as f:
        data = f.read()
    lines = [line for line in data.splitlines() if line.strip()]
    try:
        records = [json.loads(line, object_pairs_hook=_pairs,
                              parse_constant=_constant) for line in lines]
        content = _semantic(records)
        sha = _digest({'schema': SCHEMA, 'content': content})
        mode = content['kind']
    except (ValueError, TypeError, KeyError, IndexError, RecursionError):
        sha = hashlib.sha256(SCHEMA.encode() + b'\0raw\0' + data).hexdigest()
        mode = 'raw'
    return {'schema': SCHEMA, 'sha256': sha, 'mode': mode, 'records': len(lines)}


def fingerprint(paths):
    """Identity of a multiset of residual files, without their path spelling.

    Accept a path or iterable of paths. Keep tree, deep-tree, joint and e-graph
    inputs in separate calls when they have different roles in the search.
    The caller may use just ``sha256`` as the content part of a stage key.
    """
    if isinstance(paths, (str, bytes, os.PathLike)):
        paths = [paths]
    files = [fingerprint_file(p) for p in paths]
    return {
        'schema': SCHEMA,
        'sha256': _digest({'schema': SCHEMA,
                           'files': sorted(f['sha256'] for f in files)}),
        'files': len(files),
        'records': sum(f['records'] for f in files),
        'conservative_files': sum(f['mode'] == 'raw' for f in files),
    }
