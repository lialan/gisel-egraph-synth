"""Analysis views of the synthesizer: AC terms, linear forms modulo 2^W and
bit slices (docs/TargetAwareViews.md).

A view is an analysis of an expression. It is never a rewrite and never a
proof. It has two uses:

* A *signature*: the canonical form of an expression in the algebra of the
  view. Two expressions with one signature have the same value when each
  read of each input is the same defined value. A signature is a grouping
  key, for statistics and to remove *identical* implementations; two
  candidates with one signature and different implementations are both
  kept. A signature says nothing about undef or poison.
* *Proposals*: replacements of a source read from its views (the folded
  AC term, the canonical linear form with its multiplications by
  constants and its shifts, the direct form of a bit slice). A proposal is
  a candidate like a term of the enumerative search: discover.py proves
  it under the facts of the instance (prove_candidates), and
  synth.Synthesizer.add generalizes it with CEGIS and width schedules.
  Definedness is decided by those proofs, not by the view. A change of
  this module changes the search, not a proof (known.search_sha).

The semantics follow GIEGraph (include/GISelEGraphSynth/GIEGraph.h):

* AC terms: the operators that gmir_ops.json marks commutative and
  associative, for which this module knows what equal leaves do and how
  constants fold (_AC). The leaves are the operands after flattening the
  nested nodes of the same operator and type. G_ADD and G_MUL keep the
  count of equal leaves, G_XOR keeps their parity, the idempotent
  operators (G_AND, G_OR, the minimum and maximum) keep one. Constants
  fold modulo 2^W; an absorbing constant is the whole term.
* Linear forms: ``c + sum(k_i * t_i) mod 2^W`` through G_ADD, G_SUB,
  negation (0 - x), G_MUL by a constant and G_SHL by a constant amount
  smaller than W. Every other subterm is a leaf ``t_i``.
* Bit slices: the bits [lo, lo + width) of a value at the position pos of
  the result, the other bits zero, through G_LSHR and G_SHL by constant
  amounts, G_AND with a contiguous mask, G_TRUNC, G_ZEXT and G_UBFX with
  constant operands.

Only scalar integers are viewed: a vector, a floating-point value and a
pointer are leaves, and so are the saturating and carry operators. A node
of ``flagged`` (nsw, nuw, disjoint, ...) is a leaf of a signature, as in
the e-graph, where flattening it is only a refinement. A proposal reads the
flag-free source: source flags only add poison (README.md, "Semantic
model"), so the proof for the flag-free source covers them.

A proposal reads each input at most once (the replacement of a rule reads
each input once, for undef inputs), and its constants are literals or
computed constants of the constant inputs of the source
(ir.is_constant_expr). A rule matches those inputs as constants
(``const_vars``) and its proof covers every value of them.
"""

import collections
import copy
import time

from . import discover
from . import ir
from . import ops

KINDS = ('ac', 'linear', 'slice')


def _smin(w):
    return 1 << (w - 1)


def _smax(w):
    return ir.mask(w) >> 1


def _sle(a, b, w):
    return ops.sx(a, w) <= ops.sx(b, w)


# Per AC operator: what equal leaves do ('count', 'parity', 'dedupe'), how
# two constants fold, the identity and the absorbing element (None: there
# is none). That the operator is commutative and associative is read from
# gmir_ops.json (ac_operator).
_AC = {
    'G_ADD': ('count', lambda a, b, w: (a + b) & ir.mask(w),
              lambda w: 0, None),
    'G_MUL': ('count', lambda a, b, w: (a * b) & ir.mask(w),
              lambda w: 1, lambda w: 0),
    'G_XOR': ('parity', lambda a, b, w: a ^ b, lambda w: 0, None),
    'G_AND': ('dedupe', lambda a, b, w: a & b, ir.mask, lambda w: 0),
    'G_OR': ('dedupe', lambda a, b, w: a | b, lambda w: 0, ir.mask),
    'G_UMIN': ('dedupe', lambda a, b, w: min(a, b), ir.mask, lambda w: 0),
    'G_UMAX': ('dedupe', lambda a, b, w: max(a, b), lambda w: 0, ir.mask),
    'G_SMIN': ('dedupe', lambda a, b, w: a if _sle(a, b, w) else b,
               _smax, _smin),
    'G_SMAX': ('dedupe', lambda a, b, w: b if _sle(a, b, w) else a,
               _smin, _smax),
}


def ac_operator(op):
    """(multiplicity, fold, identity, absorbing) of the operator key
    ``op``, or None if the views do not flatten it. gmir_ops.json (the
    property table of GIEGraph) must say that the operator is commutative
    and associative."""
    if op not in _AC or not ops.known(op):
        return None
    meta = ops.parse(op)[0].meta
    if not (meta.get('commutative') and meta.get('associative')):
        return None
    return _AC[op]


def _scalar(w):
    return isinstance(w, int) and not ops.lanes(w)


def _lit(w, k):
    return ('lit', w, k)


# ------------------------------------------------------------ signatures --

class Canon:
    """Canonical forms of the expressions over variables of the widths
    ``vw``. ``consts`` has the value of each constant input (or None): a
    constant input is then a constant of the forms. A node of ``flagged``
    is a leaf. ``mode`` 'ac' gives AC forms, 'linear' also linear
    forms."""

    def __init__(self, vw, consts=None, flagged=(), mode='ac'):
        self.vw = tuple(vw)
        self.consts = tuple(consts) if consts is not None else \
            (None,) * len(self.vw)
        self.flagged = frozenset(flagged)
        self.mode = mode
        self._forms = {}
        self._consts = {}

    def width(self, e):
        return ir.width(e, self.vw)

    def const(self, e):
        """The value of ``e`` if it is a constant: a constant input, a
        literal, a constant, or an operation of them; else None."""
        if e in self._consts:
            return self._consts[e]
        v = self._const(e)
        self._consts[e] = v
        return v

    def _const(self, e):
        if ir.is_var(e):
            c = self.consts[e[1]] if e[1] < len(self.consts) else None
            if c is None or not _scalar(self.vw[e[1]]):
                return None
            return c & ir.mask(self.vw[e[1]])
        if not ir.is_op(e):
            return ir.leaf_value(e) if _scalar(e[1]) else None
        if not _scalar(e[1]) or not ops.known(e[0]) or \
                ir.result_kind(e) not in (None, 'i'):
            return None
        vals = [self.const(a) for a in e[2:]]
        if any(v is None for v in vals):
            return None
        info = ops.parse(e[0])[0]
        if not info.strict or info.eval is None or \
                ir.has_unspecified(e):
            return None
        v = ir.apply_op(e[0], e[1], [self.width(a) for a in e[2:]], vals)
        return None if v is None or v is ir.UB else v

    def of(self, e):
        if e not in self._forms:
            self._forms[e] = self._of(e)
        return self._forms[e]

    def _of(self, e):
        c = self.const(e)
        if c is not None:
            return ('const', self.width(e), c)
        if not ir.is_op(e):
            return e
        w = e[1]
        if e not in self.flagged and _scalar(w):
            if self.mode == 'linear' and linear_root(e, self):
                return self._linear(e)
            if ac_operator(e[0]):
                return self._ac(e)
        args = tuple(self.of(a) for a in e[2:])
        if ops.known(e[0]) and ir.is_commutative(e[0]):
            args = tuple(sorted(args[:2], key=repr)) + args[2:]
        return (e[0], w) + args

    def _ac(self, e):
        op, w = e[0], e[1]
        mult, fold, ident, absorb = ac_operator(op)
        k = ident(w)
        leaves = []
        for x in flatten(e, self.flagged):
            f = self.of(x)
            if f[0] == 'const':
                k = fold(k, f[2], w)
            else:
                leaves.append(f)
        if absorb is not None and k == absorb(w):
            return ('const', w, k)
        leaves = multiplicity(leaves, mult)
        if not leaves:
            return ('const', w, k)
        kc = None if k == ident(w) else k
        if len(leaves) == 1 and kc is None:
            return leaves[0]
        return ('ac', op, w, tuple(sorted(leaves, key=repr)), kc)

    def _linear(self, e):
        w = e[1]
        c, terms = linear_form(e, self)
        terms = tuple(sorted(terms.items(), key=repr))
        if not terms:
            return ('const', w, c)
        if len(terms) == 1 and terms[0][1] == 1 and c == 0:
            return terms[0][0]
        return ('lin', w, c, terms)


def multiplicity(leaves, mult):
    """The leaves of an AC term after the multiplicity rule ``mult``:
    'count' keeps every leaf, 'parity' one of each leaf that occurs an odd
    number of times, 'dedupe' one of each."""
    if mult == 'count':
        return list(leaves)
    counts = collections.OrderedDict()
    for f in leaves:
        counts[f] = counts.get(f, 0) + 1
    if mult == 'parity':
        return [f for f, n in counts.items() if n % 2]
    return list(counts)


def flatten(e, flagged=()):
    """The leaves of the AC term of the node ``e``: its operands, through
    the unflagged nodes of the same operator and type. A flagged node has
    its two operands as leaves (GIEGraph::getACViews)."""
    if e in flagged:
        return list(e[2:])
    out = []

    def walk(x):
        if ir.is_op(x) and x[0] == e[0] and x[1] == e[1] and \
                x not in flagged:
            for a in x[2:]:
                walk(a)
        else:
            out.append(x)
    for a in e[2:]:
        walk(a)
    return out


def linear_root(e, canon):
    """True if the node ``e`` is an operation of a linear form: G_ADD,
    G_SUB, G_MUL with a constant operand, G_SHL by a constant amount
    smaller than the width."""
    op, w = e[0], e[1]
    if not ir.is_op(e) or not _scalar(w) or e in canon.flagged:
        return False
    if op in ('G_ADD', 'G_SUB'):
        return True
    if op == 'G_MUL':
        return canon.const(e[2]) is not None or \
            canon.const(e[3]) is not None
    if op == 'G_SHL':
        s = canon.const(e[3])
        return s is not None and s < w
    return False


def linear_form(e, canon):
    """(c, {leaf form: k}) of ``e`` modulo 2^W, W the width of ``e``: the
    value is c + sum(k * leaf), and no k is 0. A leaf is the canonical form
    (``canon``) of a subterm that is not linear."""
    w = canon.width(e)
    m = ir.mask(w)

    def walk(x):
        c = canon.const(x)
        if c is not None:
            return c & m, {}
        if ir.is_op(x) and x[1] == w and linear_root(x, canon):
            op = x[0]
            if op in ('G_ADD', 'G_SUB'):
                ca, ta = walk(x[2])
                cb, tb = walk(x[3])
                s = 1 if op == 'G_ADD' else m
                out = dict(ta)
                for k, v in tb.items():
                    out[k] = (out.get(k, 0) + s * v) & m
                return (ca + s * cb) & m, out
            if op == 'G_MUL':
                k, t = canon.const(x[3]), x[2]
                if k is None:
                    k, t = canon.const(x[2]), x[3]
            else:
                k, t = (1 << canon.const(x[3])) & m, x[2]
            ct, tt = walk(t)
            return (ct * k) & m, {f: (v * k) & m for f, v in tt.items()}
        return 0, {canon.of(x): 1}
    c, terms = walk(e)
    return c, {k: v for k, v in terms.items() if v}


def ac_signature(e, vw, consts=None, flagged=()):
    """The AC form of ``e``: each AC term flattened, with the multiplicity
    rule of its operator and its constants folded modulo 2^W."""
    return Canon(vw, consts, flagged, 'ac').of(e)


def linear_signature(e, vw, consts=None, flagged=()):
    """The linear form of ``e``: each linear term as
    ('lin', W, c, ((leaf, k), ...)) modulo 2^W, the other AC terms as in
    ac_signature."""
    return Canon(vw, consts, flagged, 'linear').of(e)


class Slice:
    """The value ((base >> lo) & mask(width)) << pos of width ``w``, the
    other bits zero; ``base`` has the width ``wb``. A slice without bits
    (``width`` 0) is the value 0 and has no base."""

    __slots__ = ('base', 'lo', 'width', 'pos', 'w', 'wb')

    def __init__(self, base, lo, width, pos, w, wb):
        if width <= 0:
            base, lo, width, pos, wb = None, 0, 0, 0, None
        self.base, self.lo, self.width = base, lo, width
        self.pos, self.w, self.wb = pos, w, wb

    def key(self):
        return (self.base, self.lo, self.width, self.pos, self.w, self.wb)

    def __repr__(self):
        return 'Slice(%r, lo=%d, width=%d, pos=%d, w=%s)' % (
            self.base, self.lo, self.width, self.pos, self.w)


def _contiguous(m):
    """(lo, hi) if the ones of the mask ``m`` are the bits [lo, hi), else
    None."""
    if m == 0:
        return (0, 0)
    lo = (m & -m).bit_length() - 1
    hi = m.bit_length()
    return (lo, hi) if m == ((1 << hi) - 1) & ~((1 << lo) - 1) else None


def _leaf(e, canon):
    w = canon.width(e)
    return Slice(e, 0, w, 0, w, w)


def slice_of(e, canon):
    """The Slice of ``e``, or None if ``e`` is not an operation of a
    slice."""
    if not ir.is_op(e) or canon.const(e) is not None:
        return None
    s = _slice(e, canon)
    return None if s.key() == _leaf(e, canon).key() else s


def _slice(e, canon):
    if not ir.is_op(e) or e in canon.flagged or not _scalar(e[1]) or \
            canon.const(e) is not None:
        return _leaf(e, canon)
    op, w = e[0], e[1]
    if op in ('G_LSHR', 'G_SHL'):
        c = canon.const(e[3])
        if c is None or c >= w:
            return _leaf(e, canon)
        s = _slice(e[2], canon)
        if op == 'G_LSHR':
            return _shift_down(s, c)
        pos = s.pos + c
        return Slice(s.base, s.lo, min(s.width, w - pos), pos, w, s.wb)
    if op == 'G_AND':
        for a, b in ((e[2], e[3]), (e[3], e[2])):
            m = canon.const(b)
            if m is not None:
                r = _contiguous(m)
                if r is None:
                    break
                return _mask(_slice(a, canon), r[0], r[1])
        return _leaf(e, canon)
    if op == 'G_TRUNC':
        s = _slice(e[2], canon)
        if s.base is None or s.pos >= w:
            return Slice(None, 0, 0, 0, w, None)
        return Slice(s.base, s.lo, min(s.width, w - s.pos), s.pos, w, s.wb)
    if op == 'G_ZEXT':
        s = _slice(e[2], canon)
        return Slice(s.base, s.lo, s.width, s.pos, w, s.wb)
    if op == 'G_UBFX':
        lo, n = canon.const(e[3]), canon.const(e[4])
        if lo is None or n is None or n == 0 or lo >= w or lo + n > w:
            return _leaf(e, canon)
        return _mask(_shift_down(_slice(e[2], canon), lo), 0, n)
    return _leaf(e, canon)


def _shift_down(s, c):
    if s.base is None:
        return s
    if s.pos >= c:
        return Slice(s.base, s.lo, s.width, s.pos - c, s.w, s.wb)
    d = c - s.pos
    return Slice(s.base, s.lo + d, s.width - d, 0, s.w, s.wb)


def _mask(s, mlo, mhi):
    lo, hi = max(s.pos, mlo), min(s.pos + s.width, mhi)
    if s.base is None or hi <= lo:
        return Slice(None, 0, 0, 0, s.w, None)
    return Slice(s.base, s.lo + lo - s.pos, hi - lo, lo, s.w, s.wb)


def slice_signature(e, vw, consts=None, flagged=()):
    """('slice', w, base, lo, width, pos) of the slice of ``e`` (the base
    in its AC form), ('const', w, 0) for a slice without bits, or the AC
    form of ``e`` if it is not a slice."""
    canon = Canon(vw, consts, flagged, 'ac')
    s = slice_of(e, canon)
    if s is None:
        return canon.of(e)
    if s.base is None:
        return ('const', s.w, 0)
    return ('slice', s.w, canon.of(s.base), s.lo, s.width, s.pos)


def signature(e, vw, consts=None, kind='linear', flagged=()):
    return {'ac': ac_signature, 'linear': linear_signature,
            'slice': slice_signature}[kind](e, vw, consts, flagged)


def group(items, key):
    """The items by ``key(item)`` (a signature), in the order of their
    first member. A grouping only: no item is dropped."""
    out = collections.OrderedDict()
    for x in items:
        out.setdefault(key(x), []).append(x)
    return out


def impl_key(tgt, const_vars=()):
    """The key of identical implementations: equal modulo the order of the
    operands of commutative operators, with the same constant inputs."""
    def norm(e):
        if not ir.is_op(e):
            return e
        args = tuple(norm(a) for a in e[2:])
        if ops.known(e[0]) and ir.is_commutative(e[0]):
            args = tuple(sorted(args[:2], key=repr)) + args[2:]
        return e[:2] + args
    return (norm(tgt), tuple(const_vars))


def dedupe(cands):
    """The candidates (dicts with 'tgt' and 'const_vars') without repeated
    *identical* implementations (impl_key); the first one is kept. Two
    implementations that differ are both kept, whatever their
    signatures."""
    out, seen = [], set()
    for c in cands:
        k = impl_key(c['tgt'], c.get('const_vars', ()))
        if k not in seen:
            seen.add(k)
            out.append(c)
    return out


def group_stats(insts):
    """The signatures of the sources of ``insts``: per view the number of
    distinct signatures, and the groups and instances that share one with
    another instance (equal modulo the view; they stay instances of their
    own)."""
    out = {}
    for kind in ('ac', 'linear'):
        g = group(insts, lambda i: (
            signature(i.expr, i.vw, i.consts, kind), i.vw))
        shared = [v for v in g.values() if len(v) > 1]
        out[kind] = {'signatures': len(g), 'shared_groups': len(shared),
                     'instances_in_shared_groups': sum(map(len, shared))}
    return out


# ------------------------------------------------------------- proposals --

class Coef:
    """A constant of a view: its value in the instance and the constant
    expression that computes it when a rule applies (literals and constant
    inputs, ir.is_constant_expr). ``expr`` is None for a structural number
    that is not a literal (the 2 of x + x)."""

    __slots__ = ('w', 'value', 'expr')

    def __init__(self, w, value, expr):
        self.w, self.value, self.expr = w, value & ir.mask(w), expr

    @classmethod
    def num(cls, w, v):
        v &= ir.mask(w)
        for k in ir.LITERALS:
            if ir.lit_value(w, k) == v:
                return cls(w, v, _lit(w, k))
        return cls(w, v, None)

    def lit(self):
        """The literal of a structural constant, or None."""
        return self.expr[2] if self.expr is not None and \
            ir.is_lit(self.expr) else None

    def structural(self):
        """True if the value does not depend on a constant input."""
        return self.expr is None or ir.is_lit(self.expr)

    def key(self):
        return (self.expr, self.value) if self.expr is None else self.expr

    def __repr__(self):
        return 'Coef(%#x, %s)' % (self.value, None if self.expr is None
                                  else ir.to_sexpr(self.expr))


def _simplify(e, w):
    """Value-preserving simplifications of an operation of constant
    expressions (a constant input is never undef or poison)."""
    if not ir.is_op(e):
        return e
    op, a, b = e[0], e[2], e[3]
    zero, one, ones = _lit(w, '0'), _lit(w, '1'), _lit(w, '-1')
    if ir.is_lit(a) and ir.is_lit(b):
        v = ir.evaluate(e, (), ())
        for k in ir.LITERALS:
            if v is not None and v is not ir.UB and ir.lit_value(w, k) == v:
                return _lit(w, k)
    if op in ('G_ADD', 'G_XOR', 'G_OR') and zero in (a, b):
        return b if a == zero else a
    if op == 'G_SUB':
        if b == zero:
            return a
        if a == b:
            return zero
        if a == zero and ir.is_op(b) and b[0] == 'G_SUB' and b[2] == zero:
            return b[3]
    if op == 'G_MUL':
        if zero in (a, b):
            return zero
        if one in (a, b):
            return b if a == one else a
    if op == 'G_XOR' and a == b:
        return zero
    if op in ('G_AND', 'G_OR') and a == b:
        return a
    if op == 'G_AND' and zero in (a, b):
        return zero
    if op == 'G_AND' and ones in (a, b):
        return b if a == ones else a
    if op == 'G_OR' and ones in (a, b):
        return ones
    return e


def _coef_op(op, a, b, fold):
    """The Coef of op(a, b); ``fold`` computes the value."""
    w = a.w
    v = fold(a.value, b.value, w)
    if a.structural() and b.structural():
        # A number of the structure (literals): a literal or no form.
        return Coef.num(w, v)
    if a.expr is not None and b.expr is not None:
        return Coef(w, v, _simplify((op, w, a.expr, b.expr), w))
    c = Coef.num(w, v)
    if c.expr is None and op == 'G_MUL':
        # A structural 2 or -2 times a constant input: a shift by 1.
        for x, y in ((a, b), (b, a)):
            if x.expr is None and y.expr is not None and \
                    x.value in (2, ir.mask(w) - 1):
                e = ('G_SHL', w, y.expr, _lit(w, '1'))
                if x.value != 2:
                    e = ('G_SUB', w, _lit(w, '0'), e)
                return Coef(w, v, e)
    return c


def _add(a, b):
    return _coef_op('G_ADD', a, b, lambda x, y, w: (x + y) & ir.mask(w))


def _mul(a, b):
    return _coef_op('G_MUL', a, b, lambda x, y, w: (x * y) & ir.mask(w))


def _neg(a):
    w = a.w
    if a.expr is None:
        return Coef.num(w, -a.value)
    return Coef(w, -a.value, _simplify(
        ('G_SUB', w, _lit(w, '0'), a.expr), w))


class _Inst:
    """What the proposals read of an instance: the widths, the values of
    the constant inputs (integer scalars), and the widths of the types of
    the source."""

    def __init__(self, inst):
        self.vw = inst.vw
        self.consts = inst.consts
        self.canon = Canon(inst.vw, inst.consts, (), 'ac')
        # Without the values of the constants: two leaves are one leaf
        # of a rule only if they are one expression.
        self.sym = Canon(inst.vw, None, (), 'ac')
        self.cvars = frozenset(
            i for i, c in enumerate(inst.consts) if c is not None and
            inst.vk[i] == 'i' and _scalar(inst.vw[i]))
        self.widths = sorted({n[1] for n in ir.nodes(inst.expr)
                              if _scalar(n[1])} |
                             {w for w in inst.vw if _scalar(w)})

    def coef(self, e, w):
        """The Coef of the constant expression ``e`` of width ``w`` (a
        constant input, a literal or an operation of them), or None."""
        if self.canon.width(e) != w or \
                not ir.is_constant_expr(e, self.cvars):
            return None
        v = self.canon.const(e)
        return None if v is None else Coef(w, v, e)


def _linear_sym(e, I):
    """(constant Coef, [(leaf, Coef)]) of the linear form of ``e`` with
    the constants as constant expressions; equal leaves (their AC form
    without the values of the constants) are one leaf, in canonical
    order. None if a coefficient has no constant expression."""
    w = e[1]

    def walk(x):
        k = I.coef(x, w)
        if k is not None:
            return k, collections.OrderedDict()
        if ir.is_op(x) and x[1] == w and linear_root(x, I.canon):
            op = x[0]
            if op in ('G_ADD', 'G_SUB'):
                ra, rb = walk(x[2]), walk(x[3])
                if ra is None or rb is None:
                    return None
                (ca, ta), (cb, tb) = ra, rb
                if op == 'G_SUB':
                    cb = _neg(cb)
                    tb = collections.OrderedDict(
                        (f, (t, _neg(c))) for f, (t, c) in tb.items())
                out = collections.OrderedDict(ta)
                for f, (t, c) in tb.items():
                    out[f] = (out[f][0], _add(out[f][1], c)) \
                        if f in out else (t, c)
                return _add(ca, cb), out
            if op == 'G_MUL':
                k, t = I.coef(x[3], w), x[2]
                if k is None:
                    k, t = I.coef(x[2], w), x[3]
                if k is None:
                    return None
            else:
                s, t = x[3], x[2]
                sv = I.canon.const(s)
                if not ir.is_op(s) and not ir.is_var(s):
                    k = Coef.num(w, 1 << sv)
                elif ir.is_constant_expr(s, I.cvars):
                    # The constant 1 << s, computed when the rule applies
                    # (the guard checks that s is smaller than the width).
                    k = Coef(w, 1 << sv, ('G_SHL', w, _lit(w, '1'), s))
                else:
                    return None
            r = walk(t)
            if r is None:
                return None
            ct, tt = r
            return _mul(ct, k), collections.OrderedDict(
                (f, (u, _mul(c, k))) for f, (u, c) in tt.items())
        return Coef.num(w, 0), collections.OrderedDict(
            [(I.sym.of(x), (x, Coef.num(w, 1)))])
    r = walk(e)
    if r is None:
        return None
    c, terms = r
    return c, [terms[f] for f in sorted(terms, key=repr)]


def _scaled(t, k):
    """(expression, negated) of k * t; 'zero' for a structural 0; None if
    k has no form."""
    w = k.w
    if k.structural() and k.value == 0:
        return 'zero'
    if k.structural() and k.value == 1:
        return t, False
    if k.structural() and k.value == ir.mask(w):
        return t, True
    if k.expr is None:
        if k.value == 2:
            return ('G_SHL', w, t, _lit(w, '1')), False
        if k.value == ir.mask(w) - 1:
            return ('G_SHL', w, t, _lit(w, '1')), True
        return None
    e = k.expr
    if ir.is_op(e) and e[0] == 'G_SUB' and e[2] == _lit(w, '0'):
        r = _scaled(t, Coef(w, -k.value, e[3]))
        if r is None or r == 'zero':
            return r
        return r[0], not r[1]
    if ir.is_op(e) and e[0] == 'G_SHL' and e[2] == _lit(w, '1'):
        return ('G_SHL', w, t, e[3]), False
    return ('G_MUL', w, t, e), False


def _sum(w, parts):
    """The sum of the parts ((expression, negated) each), the positive
    ones first, or None for no part."""
    pos = [e for e, n in parts if not n]
    neg = [e for e, n in parts if n]
    if not pos and not neg:
        return None
    acc = pos[0] if pos else ('G_SUB', w, _lit(w, '0'), neg.pop(0))
    for e in pos[1:]:
        acc = ('G_ADD', w, acc, e)
    for e in neg:
        acc = ('G_SUB', w, acc, e)
    return acc


def _plus_const(w, acc, c):
    """acc + c; acc None is no term. None if c has no form."""
    if c.structural() and c.value == 0:
        return acc if acc is not None else _lit(w, '0')
    if c.expr is None:
        return None
    if acc is None:
        return c.expr
    if ir.is_op(c.expr) and c.expr[0] == 'G_SUB' and \
            c.expr[2] == _lit(w, '0'):
        return ('G_SUB', w, acc, c.expr[3])
    return ('G_ADD', w, acc, c.expr)


def linear_proposals(e, I):
    """The implementations of the canonical linear form of ``e``: the sum
    of the leaves with their multiplications or shifts and the constant,
    and the sum of the leaves times their common coefficient."""
    r = _linear_sym(e, I)
    if r is None:
        return []
    w = e[1]
    c, terms = r
    parts, kept = [], []
    for t, k in terms:
        p = _scaled(t, k)
        if p is None:
            return []
        if p != 'zero':
            parts.append(p)
            kept.append((t, k))
    out = []
    t = _plus_const(w, _sum(w, parts), c)
    if t is not None:
        out.append(t)
    keys = {k.key() for _, k in kept}
    if len(kept) > 1 and len(keys) == 1 and \
            not (kept[0][1].structural() and kept[0][1].value == 1):
        p = _scaled(_sum(w, [(x, False) for x, _ in kept]), kept[0][1])
        if p is not None and p != 'zero':
            t = _plus_const(w, _sum(w, [p]), c)
            if t is not None:
                out.append(t)
    return out


def ac_proposals(e, I):
    """The folded AC term of ``e``: the leaves that the multiplicity rule
    keeps, in canonical order, combined left to right, then the folded
    constant (an expression of the constant inputs). Where the folded
    constant has the absorbing value or the identity in the instance (but
    not for every constant input), also the absorbing literal and the term
    without the constant: those need a precondition, which CEGIS finds or
    the rule is rejected."""
    op, w = e[0], e[1]
    info = ac_operator(op)
    if info is None or not _scalar(w):
        return []
    mult, fold, ident, absorb = info
    k, consts, groups = None, [], collections.OrderedDict()
    for x in flatten(e):
        c = I.coef(x, w)
        if c is not None:
            consts.append(c)
        else:
            groups.setdefault(I.sym.of(x), []).append(x)
    for c in sorted(consts, key=lambda c: repr(c.expr)):
        k = c if k is None else _coef_op(op, k, c, fold)
    kept = []
    for f in sorted(groups, key=repr):
        xs = groups[f]
        if mult == 'count':
            kept += xs
        elif mult == 'dedupe' or len(xs) % 2:
            kept.append(xs[0])

    def build(const):
        acc = None
        for x in kept:
            acc = x if acc is None else (op, w, acc, x)
        if const is not None:
            acc = const if acc is None else (op, w, acc, const)
        if acc is None:
            acc = Coef.num(w, ident(w)).expr
        return acc
    out = []
    if k is not None and absorb is not None and k.value == absorb(w):
        lit = Coef.num(w, k.value).expr
        if lit is not None:
            out.append(lit)
    is_ident = k is not None and k.value == ident(w)
    if k is None or (is_ident and k.structural()):
        out.append(build(None))
    elif k.expr is not None:
        out.append(build(k.expr))
        if is_ident:
            out.append(build(None))
    return [t for t in out if t is not None]


def _amounts(I, v, w):
    """Expressions of the value ``v`` for an amount or the width of a
    field (an operand of any width): a constant input, or the literal 1
    of the width ``w``."""
    out = [('var', i) for i in sorted(I.cvars) if I.consts[i] == v]
    if v == 1:
        out.append(_lit(w, '1'))
    return out


def _masks(I, w, m):
    """Expressions of width ``w`` with the value ``m``: a constant input,
    a literal, -1 shifted by a constant input, or the mask of the low bits
    of a narrower type of the source."""
    out = [('var', i) for i in sorted(I.cvars)
           if I.vw[i] == w and I.consts[i] == m]
    for k in ir.LITERALS:
        if ir.lit_value(w, k) == m:
            out.append(_lit(w, k))
    for i in sorted(I.cvars):
        s = I.consts[i]
        if 0 < s < w:
            if ir.mask(w) >> s == m:
                out.append(('G_LSHR', w, _lit(w, '-1'), ('var', i)))
            if (ir.mask(w) << s) & ir.mask(w) == m:
                out.append(('G_SHL', w, _lit(w, '-1'), ('var', i)))
    for k in I.widths:
        if k < w and ir.mask(k) == m:
            out.append(('G_ZEXT', w, _lit(k, '-1')))
    return out


def slice_proposals(e, I):
    """The direct forms of the slice of ``e`` whose constants have an
    expression: the base, a mask of it, a shift of it, a G_UBFX, and a
    truncation or an extension of one of them."""
    s = slice_of(e, I.canon)
    if s is None:
        return []
    w = s.w
    if s.base is None:
        return [_lit(w, '0')]
    b, wb = s.base, s.wb

    def at_base(lo, n, pos):
        """The forms of width wb of the field [lo, lo + n) of the base
        at the position pos."""
        r = []
        if lo == pos:
            m = (ir.mask(n) << lo) & ir.mask(wb)
            if m == ir.mask(wb):
                r.append(b)
            r += [('G_AND', wb, b, x) for x in _masks(I, wb, m)]
        if pos == 0 and lo > 0:
            if lo + n == wb:
                r += [('G_LSHR', wb, b, a) for a in _amounts(I, lo, wb)]
            else:
                r += [('G_UBFX', wb, b, a, c) for a in _amounts(I, lo, wb)
                      for c in _amounts(I, n, wb)]
                r += [('G_AND', wb, ('G_LSHR', wb, b, a), x)
                      for a in _amounts(I, lo, wb)
                      for x in _masks(I, wb, ir.mask(n))]
        if lo == 0 and pos > 0 and pos + n == wb:
            r += [('G_SHL', wb, b, a) for a in _amounts(I, pos, wb)]
        return r
    if w == wb:
        return at_base(s.lo, s.width, s.pos)
    if w < wb and s.pos == 0 and s.width == w:
        # The field fills the result: the truncation of the bits from lo.
        return [('G_TRUNC', w, x) for x in at_base(s.lo, wb - s.lo, 0)
                if not (x[0] == 'G_AND' and x[2] == b)]
    if w > wb and s.pos == 0:
        return [('G_ZEXT', w, x) for x in at_base(s.lo, s.width, 0)]
    return []


class Limits:
    """The budgets of the views of one instance: the kinds that propose,
    and the most proposals that are proved (each costs a proof)."""

    def __init__(self, kinds=KINDS, max_proposals=8):
        self.kinds = tuple(kinds)
        self.max_proposals = max_proposals

    def identity(self):
        return {'kinds': list(self.kinds),
                'max_proposals': self.max_proposals}


_PROPOSERS = {'ac': ac_proposals, 'linear': linear_proposals,
              'slice': slice_proposals}


def propose(inst, dlim, limits=None, stats=None):
    """The proposals of the views of the instance ``inst``: a list of
    {'tgt', 'kind', 'const_vars'}, the cheapest first, admissible (reads
    variables of the source, each at most once, except the constant
    inputs of computed constants; well typed; operators that a rule can
    create) and within the cost bound of the search
    (discover.max_search_cost). Nothing here is proved."""
    limits = limits or Limits()
    stats = {} if stats is None else stats
    e = inst.expr
    if not ir.is_op(e) or not _scalar(e[1]) or \
            ir.result_kind(e) not in (None, 'i'):
        return []
    I = _Inst(inst)
    found = []
    for kind in limits.kinds:
        if kind == 'linear' and not linear_root(e, I.canon):
            continue
        if kind == 'ac' and (ac_operator(e[0]) is None or
                             e[0] == 'G_ADD'):
            # A sum is a linear form; its AC term is that form.
            continue
        for t in _PROPOSERS[kind](e, I):
            found.append((t, kind))
    bound = discover.max_search_cost(inst, dlim)
    # As in discover.discover: not the source, not a subtree of it (the
    # rule of the smaller pattern with that subtree as a leaf realizes
    # it), not the source with a constant input spelled as a literal.
    same = set(ir.commuted_variants(e))
    for x in ir.interior_nodes(e) + discover.literal_spellings(inst):
        same.update(ir.commuted_variants(x))
    src_vars = set(ir.variables(e))
    out = []
    for t, kind in found:
        cv = tuple(sorted({v for c in ir.computed_constants(t, I.cvars)
                           for v in ir.variables(c)}))
        if t in same:
            why = 'same_as_source'
        elif not set(ir.variables(t)) <= src_vars or \
                not ir.well_typed(t, inst.vw) or \
                ir.width(t, inst.vw) != e[1] or \
                not all(ops.creatable(n[0]) for n in ir.nodes(t)):
            why = 'not_admissible'
        elif not ir.is_linear_in(t, cv):
            why = 'reads_an_input_twice'
        elif ir.rule_cost(t, cv) > bound:
            why = 'over_cost'
        else:
            out.append({'tgt': t, 'kind': kind, 'const_vars': cv})
            continue
        stats[why] = stats.get(why, 0) + 1
    out = dedupe(out)
    out.sort(key=lambda c: (ir.rule_cost(c['tgt'], c['const_vars']),
                            KINDS.index(c['kind']),
                            ir.to_sexpr(c['tgt'])))
    if len(out) > limits.max_proposals:
        stats['proposal_limit'] = stats.get('proposal_limit', 0) + \
            len(out) - limits.max_proposals
        out = out[:limits.max_proposals]
    return out


def search(inst, backend, limits, dlim, ctx, log=None, have=()):
    """The proposals of the views of ``inst``, proved under the facts of
    the instance (discover.prove_candidates). Returns (candidates, stats):
    each candidate is {'tgt', 'family': 'views-<kind>', 'const_vars'}; the
    statistics have the prefix 'views_'. ``have`` are the replacements
    that another search of the instance proved already."""
    t0 = time.monotonic()
    st = discover.new_stats()
    st['stop'] = 'complete'
    vst = {}
    have = set(have)
    props = [p for p in propose(inst, dlim, limits, vst)
             if p['tgt'] not in have]
    for p in props:
        k = 'proposed_' + p['kind']
        vst[k] = vst.get(k, 0) + 1
    out = []
    clog = [] if log is not None else None
    if props:
        envs = discover.instance_envs(inst, dlim, ctx)
        kind = {p['tgt']: p['kind'] for p in props}
        cvs = {p['tgt']: p['const_vars'] for p in props if p['const_vars']}
        # Every proposal may be proved: the candidate limit of the search
        # applies to the terms of a bank.
        plim = copy.copy(dlim)
        plim.max_candidates = max(dlim.max_candidates, len(props))
        for c in discover.prove_candidates(
                inst, [p['tgt'] for p in props], backend, plim, ctx, st,
                envs, clog, cvs):
            k = kind[c['tgt']]
            vst['proved_' + k] = vst.get('proved_' + k, 0) + 1
            out.append(dict(c, family='views-' + k))
    stats = {'views_' + k: v for k, v in vst.items()}
    stats.update({'views_smt_checks': st['smt_checks'],
                  'views_smt_refuted': st['smt_refuted'],
                  'views_smt_unknown': st['smt_unknown'],
                  'views_stop': st['stop'],
                  'views_seconds': round(time.monotonic() - t0, 4)})
    if log is not None:
        log['views'] = {'proposals': [
            {'tgt': ir.to_sexpr(p['tgt']), 'kind': p['kind']}
            for p in props], 'candidates': clog, 'stop': st['stop']}
    return out, stats


def provenance(family):
    '''The provenance of a candidate of the family ``family`` (None for a
    candidate of the enumerative search): the views (views-<kind>) and the
    lanes of vectors (vector_search.py). The serial and the parallel search
    (parallel.py) record the same.'''
    if not family:
        return None
    if family.startswith('views-'):
        return {'discovery': family + '+smt'}
    return {'discovery': 'vector-search-%s+smt' % family}


def merge_stats(st, vst):
    '''The statistics of search() into those of the search of the
    instance: the solver counts that decide whether the search is complete
    (a stored search has no open candidate), and the views counters.'''
    st['smt_unknown'] = st.get('smt_unknown', 0) + vst['views_smt_unknown']
    # Enumeration and views can stop for different reasons. Keep both so
    # the persistent queue reopens at the budget that limited either source.
    reasons = set(st.get('limits', ()))
    reason = {'time_budget': 'time', 'proof_budget': 'proofs',
              'candidate_limit': 'candidates', 'smt_unknown': 'unknown'}.get(vst['views_stop'])
    if reason:
        reasons.add(reason)
    if vst['views_smt_unknown']:
        reasons.add('unknown')
    st['limits'] = sorted(reasons)
    if st.get('stop') == 'complete' and vst['views_stop'] != 'complete':
        st['stop'] = vst['views_stop']
    for k, v in vst.items():
        if k != 'views_stop':
            st[k] = st.get(k, 0) + v
