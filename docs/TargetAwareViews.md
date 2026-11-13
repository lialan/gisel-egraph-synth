# Target-aware views: facts, analysis views, pattern costs and tuples

This document describes the layer that GIEGraph and the rule synthesizer
share on top of the binary generic MIR operators: facts of classes, typed
constants, the definedness policy of rewrites that are not table rules,
the analysis views (AC, linear, bit slices), the tuple rules of operators
with several results, and the target costs of multi-node patterns.

Nothing here adds a second expression language. A view is an analysis of an
e-class. What it finds is added to the e-graph as ordinary binary gMIR
nodes (`G_ADD`, `G_SHL`, `G_UBFX`, ...), related to the class by a merge or a
refinement edge. Extraction, emission, the export to the synthesizer and the
proof of the synthesizer see nothing new.

```{contents}
:local:
```

## Shared semantics

One model of an operator is used by all components:

| Component | Source of the operator semantics |
|---|---|
| GIEGraph nodes, folding, rules | `OpProperties` (`lib/GIEGraph.cpp`) |
| Synthesizer typing | `gmir_ops.json`, printed from `OpProperties` (`-gisel-egraph-print-ops`) |
| Synthesizer evaluation and SMT | `girs/ops.py`, `girs/smt.py`, checked against the fold functions of `OpProperties` (`check-ops`) |
| Table rules | derived from `OpProperties`, proved by `tools/gisel-egraph/verify_rules.py` |
| Views and tuple rules | the same operators; soundness by `classifyLeafReads` (below) |

Properties that hold only under conditions are not applied unconditionally:

* commutativity and associativity are canonical forms only for unflagged
  nodes of integer types; a flagged node (`nsw`, `nuw`, `disjoint`, ...) is
  a leaf of an AC term and of a linear form;
* floating-point, saturating, carry and pointer operators are not part of
  the AC, linear or slice views;
* a vector is never one wide integer: every fact and constant of a fixed
  vector is per lane, in the width of the element.

### Equality and refinement

A merge asserts equality in both directions; a refinement edge `From ~> To`
only allows replacing uses of `From` by `To`. Every rewrite outside the
table rules is classified by `classifyLeafReads(G, Leaves)` from the number
of times each side reads each leaf class, with the same policy as the
classification of the table rules (`RewriteRule::isExactFor`):

| Change of reads of a leaf | Exact (merge) | Refinement | Unsafe |
|---|---|---|---|
| once on each side | always | | |
| fewer reads, at least one (`x + x -> x << 1`) | leaf not undef | otherwise | |
| dropped (`x ^ x -> 0`, `0 * x -> 0`) | not poison, and not undef if read more than once | otherwise | |
| more reads on the right (`x << 1 -> x + x`) | leaf not undef | | otherwise |
| read only by the right-hand side | neither undef nor poison | | otherwise |

The caller must establish the preconditions: on defined values both sides
are equal, and each side is poison exactly when a leaf it reads is poison
(no flags, no division, no select arm). `relateClasses` turns the result
into a merge, a refinement edge or nothing.

`G_FREEZE` keeps the identity of its instruction (two freezes of one value
are two classes), and the facts of `freeze(x)` are those of `x` only if `x`
is neither undef nor poison.

## Facts of classes

`EClass::Known` and `EClass::KnownLocal` are the known bits of the value of
the class (of each lane of a fixed integer vector), computed in
`EGraph::rebuild` from all nodes of the class:

* transfer functions of `llvm::KnownBits` for the integer operators
  (add, sub, mul, logic, shifts by a constant inside the width, extensions,
  truncation, `G_SEXT_INREG`, bit-field extracts, min/max, select, abs,
  byte swap, bit counts, comparisons, PHIs, the lane operators);
* the facts of the nodes of one class are joined (`unionWith`); a class
  whose facts conflict has no value that is not poison and gets none;
* `KnownLocal` uses nothing about the inputs: its facts follow from the
  expression itself (`FactSource::Structure`). `Known` also uses *context
  facts*: the known bits of the inputs (`InputInfo::Known`) and the seeds
  of classes (`EClass::Seed`, `EGraph::setKnownBits`), which the pass sets
  from `GISelValueTracking` for every register of the region, input or
  not (`FactSource::Context`). The seeds of merged classes are joined.

Facts hold for each value of the class that is not poison, in every block
where the value is used (they are properties of SSA values, not of a
control-flow path), and they are recomputed after every rebuild, so a merge
never leaves stale facts. A refinement edge carries no facts. Facts are
never a reason to merge classes by themselves; they only enable rewrites
whose result is classified as above. Register banks, use counts and costs
are not facts.

### Rules with a precondition on facts

A table rule can have a fact precondition (`RewriteRule::setFactFn`). It is
tested on `KnownLocal` first and then on `Known`; the match records which
source it needed. The rules are proved by `verify_rules.py` with the
precondition as a property of the values:

| Rule | Precondition |
|---|---|
| `add-disjoint-to-or`, `or-disjoint-to-add`, `xor-disjoint-to-or` | no bit is one in both operands |
| `and-mask-of-known-zeros` (`a & c -> a`) | every bit of `a` outside of `c` is zero |
| `or-mask-of-known-ones` (`a \| c -> a`) | every bit of `c` is one in `a` |

`or-disjoint-to-add` lets an or of packed fields reach the arithmetic
rules and the fused adds of the target (`v_lshl_add_u32`, `v_add3_u32`):
on `amdgcn.bitcast.512bit.ll` 164 instructions fewer, and only with the
facts, the pattern costs and the DAG extraction together (removing any one
of them cancels it). It was left out at first because on a memset of a
variable byte it cost up to 16 instructions per function. That was not the
multiplication that the rules can make of a splat (`b * 0x10101`) but two
losses of a CSE: equal-cost forms of the splat in neighbouring regions, and
a dominated block whose copy of the splat was rewritten (cheaper inside its
region, but no longer equal to the copy that MachineCSE removes). The
extraction now keeps the original instructions on a tie ("The original
instructions on a tie") and regions leave out instructions that a
dominating block computes already (docs/GIEGraphCombiner-Design.md,
"Region discovery"); with both, the memset file is 6 instructions smaller
with the rule than without it.

A class whose bits are all known is related to that constant
(`known-constants`): merged if it is never poison, refined otherwise.

When a rewrite needed context facts, the export record lists the rule in
`context_facts`; the synthesizer then proves the candidate with the known
bits of the inputs of the record and derives a guard (CEGIS over known-bit
atoms). A rule whose precondition follows from its left-hand side gets no
guard. A precondition that cannot be expressed as a guard is never dropped:
the candidate is rejected and counted.

## Typed constants

| Query | Meaning |
|---|---|
| `getSplatConstant(C)` (`getScalarOrSplatConstant`) | the scalar constant, or the element of a constant splat |
| `getLaneConstant(C, I)` | `Constant` (value of lane `I`), `NoValue` (a shuffle lane with mask `-1`), or `Unknown` |
| `isAllZero(C)`, `isAllOnes(C)` | the scalar, or every lane, is that exact constant |
| `addConstantSplat(Ty, V)` | a scalar constant, or a `G_BUILD_VECTOR` of one constant class |

None of them follows refinement edges, and a lane that may be undef or
poison is never a constant.

## Feature switches and statistics

`SaturationLimits::EnableFacts`, `EnableLinear`, `EnableSlice` and
`EnableTuples` turn the parts of the engine off; the pass sets them from
`-gisel-egraph-features=` (`facts`, `linear`, `slice`, `tuples`,
`patterns`, `banks`, `dag`, `all`, `none`, and `no-<name>`). With `none` the
pass is the engine before these features, for comparisons.
`SaturationStats::Views` has per view: views computed, implementations
added, merges, refinements, rewrites rejected as unsafe, views abandoned at
a budget, views outside the supported subset, and applications that needed
context facts. The report (`-gisel-egraph-report`), `-stats` and the export
record (version 3: `features`, `views`, `context_facts`) show them.

## AC views

AC canonical forms and AC matching are described in
`GIEGraphCombiner-Design.md` (AC terms). The terms are multisets of leaves;
what happens to repeated leaves depends on the operator, and every rewrite
that changes the number of reads of a leaf is a table rule with the usual
classification:

| Operator | Repeated leaf | Constants |
|---|---|---|
| `G_ADD` | kept (`a + a` stays two reads; `add-self` and the linear view relate it to `a << 1`) | folded modulo `2^W` (`fold-add`) |
| `G_XOR` | a pair cancels (`xor-self`): exact only for a leaf that is neither undef nor poison | folded |
| `G_AND`, `G_OR` | deduplicated (`and-self`, `or-self`): exact only for a leaf that is not undef | masks folded |
| `G_MUL` | kept | folded |

Merges: after every rebuild `canonicalizeAC` flattens the terms again, so a
term whose leaves became one class (`(a + b) + c` once `a == b`) gets the
canonical form of its new multiset, and terms of the same multiset meet.

Cycles: flattening goes through the first unflagged node of the operator in
each operand class, except through a class on the current path, and except
through a class whose flattening has a leaf that is the class itself or
uses it as an operand. Such a cycle appears after a merge, e.g. `x + 0`
merged with `x`, or `y` merged with `(y - x) + x`; expanding through it
would not simplify the term and would make every term that uses the class
larger. A flattening over the leaf budget keeps a prefix of its leaves, and
a cycle in the prefix still makes the class a leaf.

Several decompositions of one class (two AC nodes in one class) give several
views for matching (one per node), each flattened consistently through the
first node of every operand class; the leaves of two decompositions are
never combined in one view. Nothing is deleted: an inner sum that another
node uses stays available, and extraction counts it once.

Budget: a flattening with more than `MaxACLeaves` leaves (8,
`-gisel-egraph-max-ac-leaves`) is abandoned and the term keeps its
node-by-node form; equalities that congruence finds (regrouped prefixes)
are still found. Canonicalization stops adding nodes at `MaxNodes`.

`SaturationStats::Views` `"ac"` counts, over all canonicalization passes of
a saturation (several per iteration): the flattenings with three or more
leaves (`Views`), the canonical forms that added nodes (`Candidates`), the
merges (equal to `SaturationStats::ACMerges`), the flattenings abandoned at
`MaxACLeaves` and the stops at `MaxNodes` (`Budget`), and the flagged AC
nodes, which stay leaves (`Unsupported`). Flattenings that the matcher
abandons (`getACViews`) are not counted.

## Linear view

`applyLinearViews` (`lib/GIEGraphLinear.cpp`, `SaturationLimits::EnableLinear`,
`-gisel-egraph-features=linear`) sees a class of integers as the linear form

    c + k_1 * t_1 + ... + k_n * t_n   (modulo 2^W)

where `W` is the width of the integer, or of the element of a fixed vector
(lane by lane, never as one wide integer). The coefficients `k_i` and the
constant `c` are `APInt`s of width `W`, so they wrap around exactly like the
operators: `x * 2^31 + x * 2^31` is `0` in 32 bits.

### Decomposition

The decomposition goes through these nodes, all without flags:

| Node | Form |
|---|---|
| `G_ADD a, b` | `form(a) + form(b)` |
| `G_SUB a, b` (`0 - b` is a negation) | `form(a) - form(b)` |
| `G_MUL a, k` with a constant `k` (either operand) | `k * form(a)` |
| `G_SHL a, s` with a constant `s < W` | `2^s * form(a)` |
| a constant (`getSplatConstant`) | `c` |

Everything else is a leaf `t_i`: inputs, other operators, flagged nodes
(`nsw`, `nuw`, ... add poison), products of two non-constants (there is no
polynomial expansion), shifts by a variable or by `W` or more (`x << 32` is
poison in 32 bits, not `0`), and casts (a form has one width). In each class
the decomposition takes the first such node, in the order of the class. A
class is a leaf if it is being decomposed already, or if its decomposition
has a leaf that is the class itself or uses it as an operand: after a merge
such as `y == (y - x) + x`, expanding `y` only restates it. Leaves are
merged by canonical class id. Each leaf records how many times the
decomposition reads it, one read per occurrence: `(x << 3) + x` reads `x`
twice and has the coefficient 9.

Types: integer scalars, and fixed vectors of integers whose constants are
all splats. A vector constant with different lanes would need a coefficient
per lane; such a view is not supported (`ViewStats::Unsupported`), as is a
class of pointers, floating-point values or a scalable vector.

### Implementations

The canonical implementation of a form is built from ordinary binary nodes:

| Coefficient `k` | Term | Part |
|---|---|---|
| `1` | `t` | added |
| `2^s` | `t << s` | added |
| `-1` | `t` | subtracted |
| `-2^s` | `t << s` | subtracted |
| other | `t * k` | added |

The added terms and the constant form the AC sum `P`, the subtracted terms
the AC sum `N`, both in the canonical order of `EGraph::addACTerm`, so they
are the canonical forms that `canonicalizeAC` would build. The
implementation is `P` (with the constant as a leaf), `c - N` without added
terms, or `(P - N) + c`; a form without terms is the constant. The shift
amounts have the type of the value. Two classes with the same form get the
same implementation by hash-consing, so they become one class when both
relations are exact.

A product `t * k` whose coefficient has two set bits, `2^a + 2^b`, or is a
run of ones, `2^a - 2^b` (also for a negative `k`, e.g. `-3 = 2^0 - 2^2`),
also gets the form `(t << a) +/- (t << b)` in its class. That form reads `t`
twice, so it needs a `t` that is not undef.

The original nodes stay in the class; extraction chooses. Extraction only
takes a refinement edge that is strictly cheaper, and with the default
costs a tie keeps the original: `((a << 3) + a) - (b + b) + 7` (form
`9a - 2b + 7`) is not rewritten to `a * 9 - (b << 1) + 7`.

### Which classes

The view is computed for every class with a node of the table above, and
recomputed in every iteration (no cache: classes change with merges). It
adds nodes only where the form shows something that the nodes do not:

* the canonical implementation has fewer operations than the
  decomposition, or
* the relation is exact and the form has like terms (a leaf read twice), a
  zero coefficient, or folds two constants (equal forms then meet).

Otherwise, with two or more operators, the canonical implementation is only
looked up (no new node; an existing class with the same form is related),
and with one operator (`a + b`, `x * 3`) there is nothing to do.

### Soundness

When every read of every leaf is the same value that is neither undef nor
poison, the class and an implementation compute the same polynomial of
degree one in the integers modulo `2^W` (a shift by `s < W` multiplies by
`2^s`). Both sides consist of operators without poison-generating flags,
with shift amounts in range and without division, so each side is poison
iff a leaf that it reads is poison. These are the preconditions of
`classifyLeafReads`. The left-hand side reads each leaf as often as the
decomposition does (each class equals each of its nodes, so expanding a
class into the chosen node is exact), the canonical implementation once per
leaf with a nonzero coefficient, a shift-add form twice. `relateClasses`
then merges, adds a refinement edge, or does nothing:

| Rewrite | Merged if | Otherwise |
|---|---|---|
| `x + x - x -> x` (3 reads, 1 read) | `x` not undef | refinement |
| `x - x + y -> y` (`x` dropped) | `x` neither undef nor poison | refinement |
| `(x << 3) + x -> x * 9` | `x` not undef | refinement |
| `x * 9 -> (x << 3) + x` (2 reads) | `x` not undef | nothing (unsafe) |
| `x * 2^31 + x * 2^31 -> 0` | `x` neither undef nor poison | refinement |

### Budgets and statistics

| Budget | Default | Over budget |
|---|---|---|
| `MaxViewTerms` | 8 | distinct leaves of one view: the view is abandoned |
| `MaxViewVisits` | 64 | classes visited by one decomposition (a shared class once per use): abandoned |
| `MaxViewCandidates` | 3 | implementations of one view, the canonical one first and then one shift-add form per product: the rest is dropped |
| `MaxNodes` | 5000 | no more nodes; views that only look their implementation up still relate it |

Each stop is counted once in `ViewStats::Budget`, and the class keeps its
node-by-node form. The pass uses the defaults. `SaturationStats::Views`
`"linear"` counts the views computed (`Views`), the implementations related
(`Candidates`), the merges and refinement edges, the rewrites that
`classifyLeafReads` rejected (`Unsafe`: shift-add forms of terms that may be
undef), the budget stops and the unsupported views. `applyLinearViews`
returns the number of new nodes, merges and refinement edges.

### Effect and limitations

On `(x * 3) + (y * 2) - (x + x + x)` the view relates the root to `y << 1`
in the first iteration (19 nodes for inputs that may be undef, 21 merged for
defined ones). The table rules alone find it in the 5th (4th) iteration with
136 (128) nodes. With the default budget the graph saturates after 9
iterations with 221 nodes (5 iterations, 61 nodes for defined inputs), where
the rules alone stop at the iteration limit with 222 (195) nodes
(`unittests/GIEGraphLinearTest.cpp`). In MIR,
`test/AMDGPU/egraph-combiner-linear.mir` has a cancellation over three
values that the rules do not finish within the default iteration limit.

* The negation rules (`sub-to-add-neg`, `add-neg-to-sub`, `neg-mul`,
  `neg-sub`, ...) with AC extension keep producing new forms of the same
  combination `k * x + m * y`, and the view's nodes and merges were more
  material for them: the graph ended larger with the view than without it
  on some cancellations. They therefore do not apply at a class that the
  view related to its canonical implementation (`EClass::LinearForm`,
  `RewriteRule::skipsLinearForms`, `SaturationLimits::LinearSkipsNegation`,
  `-gisel-egraph-linear-guard`); there the canonical form already is the
  combination. The factoring rules still apply: they reach products of
  sums (`(a + b) * 3` for `3a + 3b`) that the canonical form does not
  have. On 24 runs (12 linear expressions, defined inputs and inputs that
  may be undef, full saturation with the default budget), the graph has
  fewer or as many nodes with the guard as without it in all 24, with the
  same extracted cost: `7x - 6x` 24 nodes instead of 164, `(a + b) +
  (a - b)` 183 instead of 590, `3x + 2y - (x + x + x)` with inputs that
  may be undef 26 instead of 221. Against the rules without the view it
  has fewer nodes in 15 runs, as many in 4 and more in 5: twice
  `(2x + 1) * 3 - 6x` (34 and 24 instead of 22, where the view finds the
  constant 3 and the rules do not), `(x << 1) + (x << 2) + x` (33 instead
  of 29), and twice `(x - 1) + (y + 1)` (155 instead of 103, at the
  iteration limit either way: `add-negconst`, which gives a sum with a
  negative constant its subtraction form, is not guarded). On the
  validation corpus the guard changes one file (`srem64.ll`, 2
  instructions fewer), with 1.2% fewer nodes after saturation, 2.3% fewer
  iterations and 9.4% fewer rule matches.
* One decomposition per class (its first linear node); another node of the
  class is only used through the classes that contain it.
* A shift amount of an implementation has the type of the value; after the
  legalizer such a shift may not be legal (`G_SHL s64, s64` on AMDGPU), and
  extraction then does not take it.
* No coefficients per lane (vector constants that are not splats) and no
  products of non-constants.

## Bit-slice view

`applySliceViews` (`lib/GIEGraphSlice.cpp`) sees an integer class `C` of
`W` bits as an extension of a range of bits of a class `S` of `WS` bits:

```
C == E_W(S[Lo +: N])      0 <= Lo,  Lo + N <= WS,  1 <= N <= W
```

`S[Lo +: N]` is the `N`-bit value of the bits `[Lo, Lo + N)` of `S`, and
`E` is a zero or a sign extension to `W` bits (none if `N == W`). Only
scalars have views: the bits of a fixed vector are lanes, never one integer,
and a vector class with a slice operator is counted as `Unsupported`.

### Steps

A view is a composition of steps. A step through a node of a class `D`
writes the field `D[Lo +: N]` as a field of an operand, extended if the
field also covers bits that the node fills (`i` is a bit of `D`):

| Node | Bit `i` of `D` | Condition |
|---|---|---|
| `G_LSHR s, k` | `s[k + i]`; 0 from `W - k` | `k` a constant `< W` (otherwise poison) |
| `G_ASHR s, k` | `s[k + i]`; the sign bit `s[W - 1]` from `W - k` | `k < W` |
| `G_SHL s, k` | `s[i - k]` | `k < W`, and the field is above bit `k` |
| `G_AND y, x` | `y[i]` where `x` is one, 0 where it is zero | the known bits of `x` in the field: low ones, then zeros |
| `G_OR y, x`, `G_XOR y, x` | `y[i]` | `x` is known zero in the field |
| `G_TRUNC s` | `s[i]` | |
| `G_ZEXT s`, `G_SEXT s` | `s[i]`; 0 or the sign bit of `s` above it | |
| `G_ANYEXT s` | `s[i]` | the field is inside `s` (the high bits are not specified) |
| `G_SEXT_INREG s, b` | `s[i]`; the sign bit `s[b - 1]` from `b` | `1 <= b <= W` |
| `G_UBFX s, p, w`, `G_SBFX s, p, w` | `s[p + i]`; 0 or `s[p + w - 1]` from `w` | constants with `w >= 1`, `p + w <= W` (otherwise poison) |
| `G_EXTRACT s, o` | `s[o + i]` | `o + W <= WS` |
| result `j` of `G_UNMERGE_VALUES s` | `s[j * W + i]` | |
| `G_MERGE_VALUES p_0, p_1, ...` | bit `i - j * Wp` of the part `p_j` | the field is inside one part |

A constant is an operand whose bits are all known, so one rule covers a
mask of low bits (`(x >> 8) & 0xff`), the mask of a shifted field
(`(x & 0xff00) >> 8`) and a concatenation as an OR of extensions,
`or(zext(a), shl(zext(b), Wa))`: in the high part of the OR, `zext(a)` is
known zero, so the field is a field of `shl(zext(b), Wa)` and then of `b`.
The known bits of the structure (`KnownLocal`) are tried first; the context
facts of the inputs only with the facts feature, and `ContextFacts` counts
the relations that needed them.

Extensions compose: the zero extension of a narrower field is a zero
extension of it, also inside a sign extension (its top bit is 0); a sign
extension inside a sign extension (or the whole value) is a sign extension;
a sign extension inside a zero extension is neither, and the view stops
there. A field of zeros is a constant, not a slice (the known-constants
rule relates such classes); a field of copies of a sign bit is the sign
extension of that bit.

The search is depth-first over the nodes of the classes, with the result
for each (class, field, extension) memoized; a state on the current path is
not entered again, so a cycle of classes ends the search. The view of a
class is the deepest composition (the most steps; then one without flags,
without context facts, with fewer dropped classes; then the first one
found). It is used only if it composes at least two operators: a single
operator is the node itself, and the table rules (`ubfx-to-shift-mask`,
`sbfx-to-shifts`, `sextinreg-to-shifts`, `extract-to-trunc-lshr`,
`zext-of-trunc-to-and`, `sext-of-trunc-to-sextinreg`, the compositions of
casts) relate it to its other forms.

### Forms

The direct forms of the view, the most direct first. Let `B` be `S` if
`W == WS`, `G_TRUNC S` if `W < WS` and the field is inside the low `W` bits,
and the extension of the view, `G_ZEXT S` or `G_SEXT S`, if `W > WS` (its
fill bits make a field that reaches the top of `S` a shift of `B`):

| Field of `B` | Zero extension | Sign extension |
|---|---|---|
| all of it (the whole `S` if `W > WS`) | `B` | `B` |
| up to the top of `S` | `G_LSHR B, Lo` | `G_ASHR B, Lo` |
| from bit 0 | `G_AND B, 2^N - 1` | `G_SEXT_INREG B, N` |
| otherwise | `G_UBFX B, Lo, N`; `G_AND (G_LSHR B, Lo), 2^N - 1` | `G_SBFX B, Lo, N`; `G_SEXT_INREG (G_LSHR B, Lo), N` |

If `W < WS` and the field reaches above bit `W`, the shift is in the type of
`S`: `G_TRUNC (G_LSHR S, Lo)` (`G_ASHR` for a sign extension) if the field
reaches the top of `S`, otherwise `G_TRUNC (G_UBFX S, Lo, N)` and
`G_AND (G_TRUNC (G_LSHR S, Lo)), 2^N - 1` (`G_SBFX`, `G_SEXT_INREG`). If
`W > WS`, also the extension of the first form in the type of `S`, e.g.
`G_ZEXT (G_UBFX S, Lo, N)`. The whole of `S` with `W == WS` is `S`:
`trunc(zext(x)) == x`.

The amount of a new shift has the type of the amount of a shift of the view
on a value of the same width, and otherwise the type of the value (as in
the IR; the legalizer adapts it). The position and width of a new
`G_UBFX`/`G_SBFX` have the type of the position of a bit-field extract of
the view on a value of the same width, and otherwise the type of the value
but at most `s32`. `LegalizerHelper` can widen the types of a bit-field
extract but not narrow them, while the legality check of the pass accepts
`NarrowScalar` before the legalizer, so a form must never need narrowing:
an `s64` position aborts the AMDGPU legalizer (`G_UBFX` is legal for
`{s32, s32}` and `{s64, s32}`), and for the same reason there is no
bit-field form of a value wider than 64 bits (`MaxBitFieldWidth`). The
forms are ordinary nodes with ordinary costs; a slice is not free. The
extractor chooses among them and the original nodes, and the legality check
of the pass applies to them like to any node (a target that lowers `G_UBFX`
does not get one).

### Definedness

On values that are neither undef nor poison every step is an identity of
bits, so the class and each form are `E_W(S[Lo +: N])`. The nodes of the
view read `S` once (each step has one operand on the path; the others are
constants), and each *dropped* class once: the other parts of a
`G_MERGE_VALUES`, and the operand `x` of an `AND`, `OR` or `XOR` that
selects the field by its known bits. Each form reads `S` once. No operator
on either side has poison or undefined behaviour of its own: amounts and
bit fields are constants inside the width (a step does not exist
otherwise), and the operators are unflagged. So each side is poison iff a
class that it reads is: a scalar is poison as a whole, and a field of `S` is
poison iff `S` is. `classifyLeafReads` with `S` read once on each side and
each dropped class once on the left gives:

* no dropped class: exact, also for an undef `S` (one read on each side);
* dropped classes that are not poison: exact (an undef one is fine: no bit
  of the field depends on it);
* otherwise a refinement `C ~> form`: `C` is poison when a dropped class is,
  the form is not.

The known bits of a dropped `x` hold for every value of `x` that is not
poison, which is when the relation claims equality. A node with a
poison-generating flag (`lshr exact`, `or disjoint`, `trunc nuw`, ...) is
stepped through as the node without the flag, which only refines it: such a
view relates the class by a refinement edge at most. The unit test
`ExhaustiveOnSmallWidths` evaluates every node of every class, and every
refinement, for all values of the inputs after the view has run on chains
of slice operators over `s8` and over concatenations of two `s4` values; it
checks the implementation, the argument above is the proof.

### Budgets and statistics

`MaxViewVisits` bounds the nodes that the search for one class visits;
beyond it the view is abandoned (`Budget`). `MaxViewCandidates` bounds the
forms of one view: the first ones are added and `Budget` is counted (the
lists above have at most three forms). `MaxViewTerms` bounds `S` and the
dropped classes together. The write phase stops at `MaxNodes`. A view
whose forms the class already has, or refines to, is not counted again:
`Views` counts the views that proposed something and `Candidates` the
forms that were not yet related to the class. Classes are visited in
increasing id and nodes in their order, so the result is deterministic.

### Not handled

* A field that is not one range of one value: a mask with two fields
  (`x & 0xf0f`), a field of shifted-in zeros (`(x << 8) >> 4`), a zero
  extension of a sign extension. The class keeps its nodes.
* A field across two parts of a merge is a field of the merge, not a
  combination of fields of the parts; a slice is never written as a
  concatenation of slices (no `G_MERGE_VALUES`, `G_INSERT` or funnel shift
  as a form).
* One view per class: the deepest. A shallower view through another node of
  the class is not added.
* `G_INSERT`, funnel shifts, rotations, `G_BSWAP` and an `G_ADD` with known
  low zeros are not steps. `G_EXTRACT` and `G_UNMERGE_VALUES` are steps but
  never forms, and `G_ANYEXT` is never a form.
* Fixed vectors (per-lane slices) are not handled.

### Comparison with the existing pipeline

The AMDGPU pre- and post-legalizer combiners include `all_combines`, whose
`form_bitfield_extract` forms one `G_UBFX`/`G_SBFX` from one shift and one
mask (`bitfield_extract_from_and`, `bitfield_extract_from_shr_and`), two
shifts (`bitfield_extract_from_shr`) or a `G_SEXT_INREG` of a shift. It
does not compose them: a bit field of a bit field stays two instructions.
The view composes any number of steps, across widths and through
concatenations. Instructions of small kernels (gfx1100, `-global-isel -O2`,
the operand loaded per lane, so the code is VALU; the total includes the
loads, the address computation and the store):

| Kernel | Stock | E-graph, `no-slice` | E-graph with the slice view |
|---|---|---|---|
| `(x >> 8) & 0xff` | 10 (`v_bfe_u32`) | 10 | 10 |
| `(x << 8) >>a 20` | 10 (`v_bfe_i32`) | 10 | 10 |
| `((x >> 4) & 0xff) >> 2 & 0xf` | 11 (two `v_bfe_u32`) | 11 | 10 (one `v_bfe_u32`) |
| `((x >>a 4) << 16) >>a 20` | 11 (`v_ashrrev_i32`, `v_bfe_i32`) | 11 | 10 (one `v_bfe_i32`) |
| `((x & 0xff00) >> 8 >> 3) & 7` | 11 (two `v_bfe_u32`) | 11 | 10 |
| `((x >> 3) & 0xfff) << 20 >>a 24` | 11 (`v_bfe_u32`, `v_bfe_i32`) | 11 | 10 |
| `trunc((x >> 20) & 0xffff) >> 4 & 0xff`, `x` i64 | 14 (`v_lshrrev_b64`, two `v_bfe_u32`) | 14 | 11 (one `v_lshrrev_b32`) |
| `(zext(lo16(x)) \| zext(hi16(x)) << 16) >> 20 & 0xff` | 14 (four VALU) | 14 | 10 (one `v_bfe_u32`) |

A single shift and mask gains nothing over the stock pipeline: the view
forms the `G_UBFX` earlier (before the legalizer), the stock combiner later.
(`-gisel-egraph-features=none` gives the same counts as `no-slice` here.)

On the 473 `.ll` tests of `llvm/test/CodeGen/AMDGPU/GlobalISel` (gfx1100,
`-global-isel -O2 -verify-machineinstrs`, the e-graph in rewrite mode at
both positions, `no-slice` against the default), 414 compile in both
configurations and 59 in neither (failures of the configuration, not of the
view). The slice view changes 51 functions in 15 files: 30 get fewer
instructions (86 in all, e.g. `v_test_uitofp_i64_byte_to_f32` 15 to 5,
`s_sext_inreg_i65_18` 10 to 3) and 21 get more (35 in all), for 60875 to
60824 instructions. The losses are the cost model, not the view: it counts
nodes and scales by width, so on SALU, where a 64-bit operation is one
instruction (`s_bfe_i64`, `s_and_b64`), the halves of a 64-bit field in two
`s32` nodes look as cheap and are one or two instructions more
(`s_sext_inreg_i64_33` 1 to 3); a tie of the DAG cost can pick a form that
reads the input directly and costs a register copy (`v_sext_inreg_i64_33`
5 to 6); a field that a store could take with `d16_hi` becomes a
`v_bfe_u32` (`store_i55`); in the 64-bit divisions of 24-bit values the
view exposes the low halves of the operands, and the e-graph then rewrites
the whole expansion of the division (51 to 48 nodes), which selects to one
or two more instructions; and the funnel shifts of `i128`, `v2i128` and
`v2i24` change in both directions (from -3 to +5 per function).

## Target pattern costs

Extraction and profitability use one cost function for a DAG of nodes,
`evaluateDag(G, CM, Dag)` (`lib/GIEGraph.cpp`), for the candidate that the
extractor chose (`Extractor::getDag`) and for the original region (the pass
builds a `CostDag` from the instructions of the region, one item per result
and per leaf). A fusion that the instruction selector already makes in the
original code is therefore not counted as a gain of the candidate.

### Three metrics

`CostVector` keeps three metrics apart:

| Metric | Meaning |
|---|---|
| `Instrs` | the estimated number of instructions: the node costs of the cost model (`DefaultCostModel` weighs a multiplication as `-gisel-egraph-mul-cost`, a division as 16 and a value wider than 32 bits as one instruction per 32 bits), replaced by the target where it knows better |
| `Bytes` | the estimated code size (a proxy): 4 bytes per instruction by default; on AMDGPU 4 for SOP1/SOP2/SOPC, VOP1/VOP2/VOPC, 8 for VOP3, 4 more for a literal |
| `Depth` | the estimated critical path (a proxy): the longest path through the DAG in latency estimates (`CostModel::getNodeLatency`: 1 for a simple operation, 4 for a multiplication, 32 for a division, per 32 bits) |

Extraction and profitability compare `Instrs`, then `Bytes`. `Depth` is only
reported; an instruction is never taken as one cycle. The report
(`-gisel-egraph-report`) prints `cost=` (instructions), `bytes=`, `depth=`
and `covers=` for the original region and the candidate.

### The pattern hook

The generic core names no instruction of a target. A cost model describes
the instructions that cover several nodes through two hooks:

* `CostModel::getItemCost(G, Dag, I)`: the cost of item `I` on its own; a
  target can use its bank state and its operands (literals).
* `CostModel::findCovers(G, Dag, Covers)`: candidate `PatternCover`s, each a
  root item, the inner items that it implements with it, and the cost of the
  one target instruction (including the copies that it needs).

`evaluateDag` applies the candidates greedily, users first (the order of the
instruction selector), and decides from the final DAG: a cover is applied only
if its root is not covered yet and each inner item is read exactly once (by
the root or by another inner item of the cover), is not a root (a value used
outside of the DAG), is not part of another cover and is not one result of an
instruction with several. So an inner value that another user still needs
keeps its cost (for `t = a + b; r = t + c; s = t ^ d`, `r` as one
`v_add3_u32` still needs `t`: no saving), and no item is subtracted twice.

### AMDGPU: the ThreeOp family

`lib/GIEGraphTargetAMDGPU.cpp` (created only for AMDGPU functions; it uses no
AMDGPU header: instructions are found by name through `TargetInstrInfo`, and
subtarget features by name through `MCSubtargetInfo::checkFeatures`) models
the three-operand VALU instructions that the selector of the pinned revision
forms from two generic operations, `Outer(Inner(x0, x1), x2)`
(`ThreeOp_i32_Pats` and `IMAD32_Pats` in `VOP3Instructions.td`):

| Instruction | Outer, inner | Feature (predicate) |
|---|---|---|
| `V_MAD_U32` | add, mul | `mad-u32-inst` (AddedComplexity 10) |
| `V_MAD_U64_U32` | add, mul | `gfx9-insts`, not `mad-intra-fwd-bug` |
| `V_XOR3_B32` | xor, xor | `gfx10-insts` |
| `V_XAD_U32` | add, xor | `gfx9-insts` |
| `V_OR3_B32` | or, or | `gfx9-insts` |
| `V_AND_OR_B32` | or, and | `gfx9-insts` |
| `V_LSHL_OR_B32` | or, shl | `gfx9-insts` |
| `V_ADD3_U32` | add, add; ptr_add, ptr_add (32-bit pointers) | `gfx9-insts` |
| `V_ADD_LSHL_U32` | shl, add | `gfx9-insts` |
| `V_LSHL_ADD_U32` | add, shl | `gfx9-insts` |
| `V_ADD_{MAX,MIN}_{I,U}32` | smax/umax/smin/umin, saddsat/uaddsat | `add-min-max-insts` |

The table is in the order in which the selector prefers the patterns when
several match one operation (measured: higher complexity first, then the
later definition). The conditions reproduce the selector and the folding of
operands after it, because the pass emits generic MIR and the selector forms
the instruction later:

* the outer operation is divergent (the pattern produces a VGPR). A uniform
  result is selected as SALU instructions: no credit (the SALU fusions
  `s_lshl{1-4}_add_u32` are not modelled);
* the inner operation is read once (`HasOneUseBinOp`) and is not a root;
* the inner operation is divergent. A uniform inner operation is an SGPR value
  that register bank legalization copies to a VGPR for the divergent outer
  one, and the selector does not look through the copy, except for the outer
  operator `cshl_32` (`V_ADD_LSHL_U32`, `GIIgnoreCopies`). Then the GISel
  predicate of `ThreeOpFrag` counts the SGPR-bank sources (the two operands of
  the uniform inner operation, constants included) against
  `getConstantBusLimit` (1 before GFX10, 2 from GFX10 on);
* for a divergent inner operation register bank legalization copies every
  uniform source to a VGPR, so that predicate always holds; `SIFoldOperands`
  then folds SGPR sources and constants back into the instruction as far as
  the constant bus allows. An inline constant is free; a literal needs a VOP3
  literal (GFX10 and later, one per instruction, it uses the bus). Every
  source that cannot be folded stays a `v_mov_b32`, which the cover counts;
* `V_MAD_U64_U32` gives one instruction only for a divergent addend and
  sources without a literal (otherwise no credit).

These conditions reproduce the measured selection of all combinations of
VGPR, SGPR, inline and literal sources of each pattern on gfx803, gfx900 and
gfx1100. The model also counts 64-bit `and`/`or`/`xor` of uniform values and
64-bit shifts as one instruction (`s_and_b64`, `s_lshl_b64`,
`v_lshlrev_b64`; the default counts two), so that splitting them into 32-bit
halves does not look free. A uniform 64-bit `and`/`or`/`xor` with a constant
that a 32-bit literal holds (0 to 2^31 - 1, where the zero and the sign
extension agree) is one instruction of 8 bytes as well
(`s_and_b64 s[0:1], s[2:3], 0xff`), and a uniform bit-field extract is 8
bytes: `s_bfe_u32` takes the offset and the width packed in one operand,
which is a literal for any width (`test/AMDGPU/egraph-combiner-salu64.*`).
A uniform 64-bit select is one `s_cselect_b64`.

The parts of a register tuple take no instruction: the 32-bit halves of a
64-bit value and the 32-bit (or 64-bit) elements of a vector are registers
of a tuple, so `G_UNMERGE_VALUES` into such parts and a truncation from 64
to 32 bits are subregisters, and `G_MERGE_VALUES`, `G_BUILD_VECTOR` and
`G_CONCAT_VECTORS` of such parts and an any-extension from 32 to 64 bits
are a `REG_SEQUENCE`; a constant part is one move into its register. A
zero or sign extension from 32 to 64 bits is one move or shift for the
high half, and a uniform one from `s1` one `s_cselect_b64`
(`test/AMDGPU/egraph-combiner-tuples.ll`). The default counts one
instruction per 32 bits for each of them, so that splitting a 64-bit
operation into its halves looked like a saving and keeping it whole looked
expensive. That made the slice view replace the 64-bit masks of the lanes
of a zero-extending load by 32-bit extracts and zero high halves
(`load-local-i8.ll`), the facts set the low half of `x << (s | 32)` to a
separate constant 0 (`shl64_reduce.ll`), and the carry of a 64-bit add
sign-extended in 32 bits and copied into the high half (`addsub64_carry.ll`).

Not modelled: the `V_MAD_U64_U32_gfx11` variant on subtargets with
`mad-intra-fwd-bug` (two or three instructions), `V_LSHL_ADD_U64`, SDWA
(`v_or_b32_sdwa` on GFX8 folds a byte mask), the moves of literals of other
VOP3-only instructions before GFX10, and uniform operations that only have a
VALU form (computed in VGPRs and read back with `v_readfirstlane`).

### Positions

| Position | Bank of a value | What the model decides |
|---|---|---|
| before the legalizer | predicted from the uniformity analysis | covers of 32-bit operations, which the legalizer keeps; 16- and 64-bit operations get no cover (they are widened or split) |
| after the legalizer, before register bank selection | predicted from the uniformity analysis | the same, on legal operations |
| after register bank selection (shadow only: the pass does not rewrite there) | read from the register banks of the function | the same; the uniform sources of a VALU operation are then already copies to VGPRs, so the count of moves can be too low |

`-gisel-egraph-report` prints the model of each function (`target-costs:`).

### Results

Instructions of the final ISA (`llc -global-isel`, without `s_waitcnt`,
`s_setpc_b64` and `s_delay_alu`) of `test/AMDGPU/egraph-combiner-add3.ll`;
"e-graph" is `-amdgpu-gisel-egraph -gisel-egraph-mode=rewrite` with all
features, "none" with `-gisel-egraph-features=none`:

| Function | gfx803 (all) | gfx900 (all) | gfx1100 stock | gfx1100 e-graph | gfx1100 none |
|---|---|---|---|---|---|
| `(a + 7) + (b + 9)` | 2 | 1 | 1 | 1 | 1 |
| `t = a + b; r = t + c; s = t ^ d` | 3 | 3 | 3 | 3 | 3 |
| uniform `(a + b) + c` | 3 | 3 | 3 | 3 | 3 |
| `(s + v) + s'` | 2 | 2 | 1 | 1 | 1 |
| `((s + s') + v) \| (v & 255)` | 3 | 4 | 3 | 2 | 3 |
| `(a << 3) + a` | 2 | 1 | 1 | 1 | 1 |
| `(s + s') << v` | 2 | 2 | 1 | 1 | 1 |

The stock pipeline already selects one `v_add3_u32` for `(a + 7) + (b + 9)`
(the pre-legalizer combiner reassociates the constants) and one
`v_lshl_add_u32` for `(a << 3) + a`; the pattern costs keep the e-graph from
calling `a * 9` a gain there (with `-gisel-egraph-mul-cost=1` the node count
does). The e-graph changes the code only where its own choice changes:
`((s + s') + v) | (v & 255)` on gfx1100, where the AC-canonical grouping
`(v + s) + s'` has a divergent inner add and one `v_add3_u32` takes the two
SGPR sources. Before GFX10 that needs a `v_mov_b32`, so the combiner keeps
the original.

### Corpus

Measured on the branch of this part alone (without the linear and slice
views), the pattern costs and the sharing-aware extraction each saved about
270 instructions on the validation corpus, mostly shifts and adds that
became one `v_lshl_add_u32`. With all parts merged the slice view takes
most of these opportunities first; see [Evaluation](#evaluation) for the
numbers of the merged pass.

## Register banks

Before register bank selection the pass predicts the bank of a value. It
computes `MachineUniformityInfo` on first use (`computeMachineUniformityInfo`
with a local `MachineCycleInfo` and the dominator tree of the pass) and again
after each rewrite. AMDGPU register bank selection of the pinned revision
(`AMDGPURegBankSelect`) puts a value in an SGPR exactly when the analysis
finds it uniform at its definition (apart from copies with an implicit use of
`exec` and lane masks, which are not region values), so the prediction is
"uniform: SGPR, divergent: VGPR (VCC for a divergent `s1`)". A uniform value
can still be computed in VGPRs (a load that cannot be scalar is a VGPR load
and a `v_readfirstlane`); the model takes it as an SGPR, which only withholds
VALU credit.

Extraction keeps at most two bank states per class (`BankState::Any` and
`BankState::Uniform`), never a Pareto frontier: the tree-cost fixpoint runs
once for each state, and in the state Uniform a node is available only if all
its operands are in that state and the cost model accepts it
(`CostModel::canBeUniform`: an input or a PHI that the analysis finds
uniform; a constant; an operation if its operands are). A new node therefore
gets its bank bottom-up: divergent as soon as an operand is. A root whose
value is uniform in the original function, and a terminator whose operands
are, must be computed in the state Uniform: extraction takes their choices in
that state, and `evaluateDag` gives an infinite cost to a DAG in which such a
root is not uniform. A uniform value is thus never computed from a divergent
one (which would need a copy from a VGPR to an SGPR, i.e. a
`v_readfirstlane`, valid only for uniform values). Copies the other way, from
an SGPR to a VGPR, are legal; they cost one `v_mov_b32` where an instruction
cannot read the SGPR (the sources of a ThreeOp instruction beyond the
constant bus). A VALU instruction with two operands reads one SGPR operand
directly, so it needs no copy.

After register bank selection the banks are read from the function (shadow
mode only). On a target without a model (AArch64) there are no bank states.
With `-gisel-egraph-features=no-banks` every value counts as divergent and the
roots have no requirement.

Not implemented: the extra `v_readfirstlane` of uniform operations without a
SALU form, the bank of `s1` values (VCC versus SGPR) in costs, and the
uniformity of values that an earlier rewrite of the same function created
before the analysis is computed again (it is recomputed after every rewrite).

## Sharing-aware extraction

The tree-cost fixpoint chooses per class the cheapest node by tree cost,
which counts a shared operand once per user. `Extractor::extract(Roots,
RootStates, CM, Opts)` then improves the choices of the classes of the DAG
by DAG cost: for a bounded number of rounds (4) it tries, for each class of
the current DAG in DAG order, each allowed node whose operands have a choice
and each refinement target, rebuilds the DAG and accepts the change if
`evaluateDag` (pattern covers, bank states, an instruction with several
results counted once) is strictly smaller. A change that makes the choices
cyclic (through refinement edges or operands) is never accepted. The search
stops after `-gisel-egraph-max-dag-evaluations` (512) evaluations per region.
It is deterministic: classes, nodes and refinement targets are visited in a
fixed order, and the first improvement is taken. By default it does not
change the choices of classes of a vector type
(`-gisel-egraph-dag-vectors`): their costs are rough (the legalizer splits or
scalarizes most vector operations), and searching over them gained nothing on
the corpus below. `-gisel-egraph-dag-size-tiebreak=false` accepts only
changes that save instructions.

Profitability compares `evaluateDag` of the candidate with `evaluateDag` of
the original region under the same model. With
`-gisel-egraph-features=no-dag` the choices are the tree-cost ones, as
before.

### The original instructions on a tie

A region is rewritten when its candidate is cheaper as a whole, but most of
its values usually cost the same in several forms. Which of them extraction
took used to be an accident of the search: the tree cost takes the first of
equal nodes, and the local search stops at the first strictly cheaper DAG.
The form of such a value matters outside of the model: another region (a
region ends at `-gisel-egraph-max-region-instrs`, and a dominated block
recomputes values of the legalizer) computes it in the original form, and
after instruction selection MachineCSE merges two equal instructions, not
two equal values. On `memset-param-combinations.ll` with
`or-disjoint-to-add`, one region took `v_add3_u32` for the byte splat
`b | b<<8 | b<<16 | b<<24` where the next regions computed the same value
with the original `v_or3_b32`: the lanes of a store were then two values
(+9 to +16 instructions of moves per function).

So the instructions of the region are preferred (`CostModel::isPreferred`;
the pass gives the instructions of the region, as nodes of the saturated
graph, `-gisel-egraph-prefer-original`):

* the tree-cost fixpoint takes a preferred node on a tie, never the other
  way (the choices stay acyclic: a chosen node costs as much as its class,
  so its operands cost less);
* the local search compares instructions, then bytes, then the number of
  operations of the DAG that are not preferred;
* a last move (`ExtractionOptions::RestoreOriginal`), for each class of the
  DAG whose choice is not preferred, chooses its preferred node and, below
  it, the preferred node of each operand class whose choice is not
  preferred, and keeps the change if the DAG costs no more and keeps more
  original instructions. The local search changes one class at a time and
  cannot reach an original form whose operand classes are not in the DAG
  (in the splat: the tree cost took a multiplication, the search found
  `v_add3_u32`, and the `v_or3_b32` needs its inner or as well).

A preferred node never wins against a cheaper one. The report prints
`original=P/N kept=K/M`: the instructions of the region that are nodes of
the saturated graph, and the operations of the candidate that are one.

## Tuples (operators with several results)

An instruction with several results is one e-node per result; extraction
counts the nodes of one instruction once (`Extractor::getMultiResultKey`) and
the emission builds it once, with one register per used result.
`applyTupleRules` (`lib/GIEGraphTuples.cpp`) adds:

* the siblings: for each node of result `i` of an operator with several
  results, the nodes of the other results with the same operands (bounded by
  `MaxNodes`). Each sibling is a new class; a table rule relates it to a
  single-result operator (`uaddo-0-to-add` merges `G_UADDO:0 a, b` with
  `G_ADD a, b`). A sibling computes nothing new: it is another result of an
  instruction with the same operands (for a division, with the same trapping
  behaviour; a division result is only refined to the single-result
  operator);
* the carry of an addition as a comparison, the table rule
  `uaddo-carry-from-icmp`, `(G_ICMP:ult (G_ADD ?a ?b) ?a) => (G_UADDO:1 ?a ?b)`
  (the matcher also finds `(a + b) <u b` and the swapped `a >u (a + b)`). On
  defined values the carry is set exactly when the wrapped sum is less than
  an operand, and both sides are poison exactly when `a` or `b` is (an
  unflagged add and compare; a flagged node is only matched as a
  refinement). The left-hand side reads `a` twice and the right-hand side
  once, so the policy of the table rules (the same as `classifyLeafReads`)
  merges the classes if `a` is not undef, and otherwise only adds the
  refinement edge comparison ~> carry: each read of an undef `a` can see
  another value, so the comparison can be true or false for any `b`, and the
  carry is one of its values; the other direction is never taken. The rule
  is printed by `-gisel-egraph-print-rules` and proved by `verify_rules.py`
  like the other rules, but it is applied by `applyTupleRules`, behind
  `-gisel-egraph-features=tuples`.

With both the sum and the carry used, the tree costs of `G_ADD` and
`G_UADDO:0` tie, and the sharing-aware extraction takes `G_UADDO:0`, so the
DAG has one `G_UADDO` (2 nodes become 1 instruction); with only the sum used
it stays a `G_ADD`; with only the carry used it is one `G_UADDO` whose sum is
unused. `G_UADDO` must be allowed at the position (`TargetCostModel`; it is
legal for `s32` on AMDGPU before and after the legalizer). External users of
either result are redirected to the result of the one instruction
(`test/AMDGPU/egraph-combiner-uaddo.mir`, with the machine verifier after the
pass).

The stock pipeline already forms `llvm.uadd.with.overflow` from `add` and
`icmp ult` in IR: CodeGenPrepare's `combineToUAddWithOverflow` does it
whenever `shouldFormOverflowOp` holds, which for AMDGPU is the default (the
operation is legal for `i32`). So an `.ll` input reaches the e-graph with a
`G_UADDO` already, and `llc -global-isel` selects one `v_add_co_u32`
(gfx900: 2 instructions for the sum and the carry as a value, with the
e-graph combiner too). The tuple rules matter for MIR in which the add and
the comparison are separate (with `-disable-cgp` the stock pipeline gives 4
instructions for the same function and the e-graph combiner 2;
`test/AMDGPU/egraph-combiner-uaddo.ll`).

## Synthesizer integration

The synthesizer (`tools/gisel-rule-synth`) reads the same operator
properties (`gmir_ops.json`) and uses the views and facts in three places.
Nothing it takes from the e-graph is trusted: every candidate is proved by
the synthesizer's own SMT model before it is a rule. The views run in the
worker processes of the parallel search (`girs/parallel.py`) exactly as in
the serial one (`--search-jobs 0`); `tests/test_views.py` checks that both
find the same rules.

* **Views as a candidate family** (`girs/views.py`). The AC, linear and
  slice views are computed on the sources of the corpus with the semantics
  of this document: AC terms of the operators that `gmir_ops.json` marks
  commutative and associative, through unflagged nodes of one integer type
  (G_ADD and G_MUL keep the count of a leaf, G_XOR its parity, the
  idempotent operators one leaf; constants fold modulo `2^W`); linear forms
  `c + sum(k * t) mod 2^W` through G_ADD, G_SUB, negation and G_MUL and
  G_SHL by constants; slices through shifts by constants, contiguous masks,
  truncations, zero extensions and G_UBFX. A flagged node, a vector, a
  floating-point, saturating or carry operator and a shift by the width
  or more are leaves. The canonical forms are signatures: grouping keys
  for statistics and for removing identical implementations, never a
  reason to drop a different implementation. The implementations of a view
  (the folded AC term, the linear form with its multiplications and
  shifts, the direct form of a slice) are proposals of the family
  `views-<kind>`: proved under the facts of the instance, then generalized
  with CEGIS and width schedules. Undef and poison are decided by those
  proofs (a proposal reads each input at most once), not by the view.
* **Facts and preconditions** (`girs/egraph.py`). An e-graph candidate is
  first proved with no fact of its inputs. If that proof holds, the
  precondition follows from the matched source (`precondition_source`
  `lhs`, no guard). If not, its known bits are the input of CEGIS, which
  finds a precondition over known-bit atoms that the emitted guard tests
  with `GISelValueTracking` (`guard`), or the candidate is rejected and
  counted (`no_precondition_in_grammar`, `solver_unknown`). The records of
  version 3 with `context_facts` are cross-checked: each one gives a guarded
  rule, a counted rejection, candidates proved without facts, or no
  candidate, and the count of each is in `rules.stats.json`
  (`egraph.context_facts`).
* **Tuples.** When the selected DAG computes two roots of a region with one
  instruction of several results (`"res"` projections of one G_UADDO), the
  root that reads the other is a seed of a rule with several outputs, which
  `region.py` proves with every output in one query. Roots that do not read
  each other are counted as a rule for several roots that the import does
  not make.

`eval/rule_chain.py` runs a conditional rule (x + y -> x | y with the guard
"no bit is one in both", found from x + 1 with the low bit of x known zero)
and the rule of a sum with its carry from a corpus to a scratch build of
llc and the lit tests of `test/SynthChain`.

## Evaluation

`tools/gisel-rule-synth/eval/views_eval.py` compiles a fixed list of `.ll`
files for gfx1100 (`-O2 -global-isel -global-isel-abort=2
-verify-machineinstrs`) in the configurations `stock` (no e-graph pass),
`none` (the pass with `-gisel-egraph-features=none`, i.e. the engine before
these features), `all` (the default) and all-but-one-feature. The measures
are static: instructions of the final assembly, encoded code size
(`codeLenInByte`), registers, CPU time and peak memory of llc. Nothing was
run on a GPU; no run-time performance is claimed.

**Validation corpus** (`manifests/amdgpu-validation.txt`, 1469 LLVM AMDGPU
tests; 1405 compile in every configuration with the same SelectionDAG
fallbacks; none fails in one configuration only):

| Configuration | Instructions | vs stock | Code bytes vs stock | Files better / worse than stock |
|---|---|---|---|---|
| stock | 296564 | | | |
| none | 296071 | -493 | -2548 | 68 / 16 |
| all | 295673 | -891 | -5148 | 93 / 32 |
| all but facts | 295690 | -874 | -5036 | 88 / 29 |
| all but linear | 295672 | -892 | -5168 | 93 / 32 |
| all but slice | 296046 | -518 | -3092 | 77 / 26 |
| all but tuples | 295673 | -891 | -5148 | 93 / 32 |
| all but patterns | 295684 | -880 | -4744 | 89 / 33 |
| all but banks | 295683 | -881 | -5768 | 91 / 34 |
| all but dag | 295702 | -862 | -4620 | 88 / 28 |

Against `none`, all features make 51 files smaller and 25 larger (the
largest: `load-local-i8.ll` +27, `load-constant-i8.ll` +13,
`urem-constant-i128.ll` +12, `shl64_reduce.ll` +11, `addsub64_carry.ll` +9;
the largest gains: `cvt_f32_ubyte.ll` -89, `fptoi.i128.ll` -73,
`load-global-i8.ll` -68, `load-global-i1.ll` -49, `permute_i8.ll` -28). The
slice view gives most of the gain (373 of 398 instructions over `none`;
then the sharing-aware extraction 29, the facts 17, the pattern costs 11,
the banks 10 and 620 bytes of code); the linear view and the tuple rules
change nothing on this corpus (the existing rules already reach the linear
cancellations in it, and CodeGenPrepare already forms
`uadd.with.overflow` from an add and a comparison). The sum of the CPU time
of llc and its peak memory (104 MiB) are within noise of `none`.

The `-stats` counters of the pass over the 99011 regions of these files
(all features against `none`): 603830 e-nodes after saturation against
580019 (+4%), 903318 rule matches against 514557 (+76%, mostly the fact
rules), 2% more iterations, 5 regions stopped by a budget against 10, and
2876 regions rewritten against 2057. With all features, 5520 rewrites were
justified by known bits (1358 of them needed facts of the inputs of the
region), the linear view made 5276 rewrites, the slice view 7347 and the
tuple rules none; 842 views were abandoned at a budget (752 of them are AC
flattenings, also counted without the features), the definedness policy
rejected 86 view rewrites, and the pattern costs found 2833 covers in the
candidates and 2811 in the original regions.

**Feature corpus** (`eval/views-corpus/`, 17 kernels, not used by any test
or by discovery): stock 190, none 184, all 182 instructions. The stock
pipeline already selects one `v_add3_u32` for `(a + 7) + (b + 9)`, one
`v_lshl_add_u32` for `(a << 3) + a` and one `v_add_co_u32` for an add with
its carry; the e-graph keeps these (no false gain). The gains are the
cancellation `(a*3) + (b*2) - (a+a+a)` (14 to 8 instructions; the engine
without the features already finds it), the nested bit field
`((x>>4)&255)>>2 & 15` (two `v_bfe_u32` to one) and one instruction from
the facts and the pattern costs together.

The comparison with `stock` includes everything the existing pipeline does
after the pass (the post-legalizer combiner, the selector's multi-node
patterns), so a rewrite that the pipeline would have done anyway is not
counted.

### Second round: ties, redundant instructions and `or-disjoint-to-add`

The same corpus and flags after the changes of the second round, each
measured on its own commit (1405 comparable files; instructions of the
final assembly):

| Commit | `all` vs stock | `none` vs stock | `all`: files better / worse |
|---|---|---|---|
| previous main (`2ae17ea`) | -891 | -493 | 93 / 32 |
| extraction keeps the original instructions on a tie | -998 | -489 | 91 / 31 |
| regions leave out instructions that a dominating block computes | -1015 | -495 | 92 / 30 |
| `or-disjoint-to-add` | -1301 | -495 | 103 / 29 |
| the fact preconditions tested before the AC pairs | -1301 (the same code in every file) | -495 | 103 / 29 |
| AMDGPU costs of register tuples and 64-bit SALU forms | -1368 | -495 | 105 / 14 |
| the negation rules do not apply at canonical linear forms | -1370 | -495 | 105 / 14 |

Against the previous main, all features now save 477 instructions and
1856 bytes more, and 14 files are worse than stock instead of 32. With all
features (`all` minus `no-<f>`): slice 507, patterns (the target model,
which now includes the costs of register tuples) 455, facts 319, dag 285,
banks 2, linear 1, tuples 0 (the previous round: 373, 11, 17, 29, 10, 0,
0). The facts, the pattern costs and the DAG extraction pay off mostly
together, as the add form of an or meets the fused adds of the target;
measured directly before the costs of register tuples,
`f:facts+patterns+dag` alone saved 765 instructions against stock (`none`
495).

| Configuration | Instructions | vs stock | Code bytes vs stock | Files better / worse than stock |
|---|---|---|---|---|
| stock | 296564 | | | |
| none | 296069 | -495 | -2528 | 67 / 18 |
| all | 295196 | -1368 | -7004 | 105 / 14 |
| all but facts | 295515 | -1049 | -6832 | 91 / 14 |
| all but linear | 295197 | -1367 | -7008 | 105 / 14 |
| all but slice | 295703 | -861 | -3984 | 88 / 14 |
| all but tuples | 295196 | -1368 | -7004 | 105 / 14 |
| all but patterns | 295651 | -913 | -4796 | 89 / 31 |
| all but banks | 295198 | -1366 | -6692 | 103 / 18 |
| all but dag | 295481 | -1083 | -5904 | 90 / 11 |

Without the scheduling and wait hints (`s_delay_alu`, `s_waitcnt`,
`s_nop`, `s_clause`, which the instruction count includes and which come
from the scheduler, not from the selected code), all features save 1204
instructions against stock and 11 files are worse (`bfm.ll`,
`integer-mad-patterns.ll` and `GlobalISel/and.ll` differ only in hints).

The files that stay worse than stock: 9 of the 14 are as worse with `none`
(the engine before these features: `uaddsat.ll` +7, where the e-graph
scalarizes a `<3 x i16>` saturating add before the legalizer, `udivrem.ll`
+4, `bfm.ll` +3, ...), and of the others `extract_vector_elt-i64.ll` +4
and `-f64.ll` +2 come from addressing modes (Limitations).

With `or-disjoint-to-add`, `memset-param-combinations.ll` is 551
instructions (557 before, 501 stock) and `amdgcn.bitcast.512bit.ll` 15485
(15649 before and stock), with 349 more `v_lshl_add_u32` and 634 fewer
`v_lshlrev_b32` over the corpus.

The fact rules with both directions of the disjoint or matched 1.93M
times over the corpus; testing the necessary condition of the
precondition on each variable before the AC pairs (`RewriteRule::
setVarFilter`) leaves 1.38M with the same code in every file. With
`or-disjoint-to-add`, 47 regions stop at a budget (5 without it).

Compile time, in CPU seconds of the pass over the corpus (`--time-passes`;
the commits measured one after the other with `-j 32`; these runs vary by
several percent, the stock compilation of the corpus by up to 10%): 11.9 s
without `or-disjoint-to-add` (saturation 5.6 s), 14.7 s with it (8.2 s),
and 15.2 s with the variable filter (8.6 s). The filter removes matches but
not time: the graphs grow by the rewrites that now fit the budget of an
iteration. The value numbering takes 0.25 s and the uniformity analysis
0.1 s; llc takes 215 to 250 s over the corpus.

The evaluation driver now measures any set of features (`f:facts+dag`),
names configurations with extra flags (`--define 'x=all -flag'`), and
records the timers of the pass (`--time-passes`: build, saturate, extract
and rewrite, and the uniformity analysis and the value numbering that it
computes again after a rewrite); `eval/views_diff.py` compares two
configurations of one or two runs file by file.

## Limitations

* The views and the facts are bounded and conservative: one decomposition
  per class for the linear and slice views, scalar slices only, no
  per-lane linear coefficients, no products of non-constants, no
  `G_SPLAT_VECTOR`, no floating point. Over budget a view is abandoned and
  counted; the class keeps its node-by-node form.
* Extraction keeps an original instruction only on an exact tie of the
  model. A rewrite that the model finds strictly cheaper still changes the
  form of a value that another region of the same block (beyond
  `-gisel-egraph-max-region-instrs`) or a sibling block computes too, and
  then MachineCSE cannot merge them. Only copies in a dominating block are
  left out of regions (value numbers of the pure instructions).
* `or-disjoint-to-add` costs about a quarter of the time of the pass
  (saturation +50%): every or with disjoint operands gets an add form that
  the arithmetic rules then rewrite further.
* The model does not see register pressure. With the costs of register
  tuples, the 64-lane zero extension of `load-global-i1.ll` is a tie
  between the 64-bit masks of the stock code and 32-bit extracts with zero
  high halves (two instructions per lane either way); the stock form keeps
  more SGPR pairs live and spills 24 of them to VGPR lanes, so the old
  model, which overcounted the 64-bit form, gained 63 instructions there by
  accident and the new one does not take them (`load-global-i1.ll` +51
  against the previous commit, still 100 below stock). Pricing only the
  casts as halves of a pair, without the merges and unmerges, lost 29
  instructions on the corpus: the tuple costs have to change together.
* A constant that a candidate returns (a root) is a move in a register that
  the model does not count; counting it gained nothing on the corpus (+2).
* Before the legalizer, the e-graph can scalarize a vector of 16-bit lanes
  (`<3 x i16>` saturating add in `uaddsat.ll`, +7 already without the
  features): the model counts the `G_BUILD_VECTOR`s of the lanes of the
  inputs, which are the packed argument registers, and not the unpacking,
  the `v_readfirstlane`s and the repacking that the scalar form takes.
* Addressing modes are not modelled: a pointer addition of a constant that
  the memory instruction folds into its offset counts as a 64-bit add, so
  `ptradd-assoc` moving the constant into an or of the index looks like a
  saving and costs an instruction (`extract_vector_elt-i64.ll` +4).
* The cost model is a static proxy: instruction count first, encoded size
  second, depth only reported. It does not model latency, register pressure
  or scheduling, SALU fusions (`s_lshl{1-4}_add_u32`), `v_readfirstlane` for
  uniform values that need VALU-only operations, or VCC versus SGPR pairs
  for `s1` values. Banks before RegBankSelect are predicted from
  uniformity.
* After the legalizer on subtargets with real 16-bit registers (gfx11 and
  later), the pass does not create new 16-bit scalar operations: a valid
  rewrite of `permute_i8.ll` was miscompiled after register allocation by
  the existing true16 code (`test/AMDGPU/egraph-combiner-true16.ll`).
* The pass is still not in any default pipeline (`-amdgpu-gisel-egraph`),
  and it does not run after RegBankSelect except in shadow mode.
* The synthesizer proves every candidate that the views propose, but on real
  corpora (taken after LLVM's own combines) the views family finds few new
  rules, and none of them has been selected for a target profile by a
  measured run; the conditional rule `x + y -> x | y` (disjoint bits) is
  shown end to end in a scratch build (`eval/rule_chain.py`), not in the
  shipped profiles, where it is an equal-cost rule.
