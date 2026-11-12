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
  expression itself (`FactSource::Structure`). `Known` also uses the
  *context facts* of the inputs (`InputInfo::Known`), which the pass takes
  from `GISelValueTracking` (`FactSource::Context`).

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
| `add-disjoint-to-or`, `xor-disjoint-to-or` | no bit is one in both operands |
| `and-mask-of-known-zeros` (`a & c -> a`) | every bit of `a` outside of `c` is zero |
| `or-mask-of-known-ones` (`a \| c -> a`) | every bit of `c` is one in `a` |

There is no `or-disjoint-to-add`: it fed bit operations into the arithmetic
rules, which replaced the shifts and ors that the AMDGPU selector fuses
(`v_lshl_or_b32`, `v_or3_b32`) by a multiplication; on the validation corpus
the facts then cost 45 instructions instead of saving any.

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
