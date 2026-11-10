# GIEGraphCombiner: an experimental e-graph combiner for GlobalISel

```{contents}
:local:
```

## Status

Experimental proof of concept. The pass is **not** part of any default
pipeline. It is reachable only through

* `llc -run-pass=gisel-egraph-combiner` (any target, MIR tests), or
* `llc -global-isel -amdgpu-gisel-egraph` (AMDGPU, after the pre-legalizer
  combiner),

and it runs in *shadow* mode (analysis only) unless
`-gisel-egraph-mode=rewrite` is given.

## Goal

GlobalISel combines are destructive, ordered, hand-written rewrites. The
pre-legalizer combiner contains many closely related integer patterns (for
example the `integer_reassoc_combines` group in `Combine.td`, `sub_add_reg`,
`add_sub_reg`, `right_identity_*`, `mul_to_shl`, `mul_by_neg_one`) that are
each a short composition of a few algebraic identities. The question this PoC
explores is whether a *small, generic, verified* rule set run under bounded
equality saturation can (a) subsume such patterns and (b) find opportunities
that greedy rewriting misses, while keeping LLVM's undef/poison semantics
intact.

## Where it runs

The current AMDGPU GlobalISel pipeline is

```
IRTranslator -> AMDGPUPreLegalizerCombiner -> Localizer -> Legalizer
  -> AMDGPUPostLegalizerCombiner -> RegBankSelect -> AMDGPURegBankCombiner
  -> InstructionSelect
```

With `-amdgpu-gisel-egraph` the e-graph combiner is inserted right after
`AMDGPUPreLegalizerCombiner` (`GCNPassConfig::addPreLegalizeMachineIR`). At
that point generic integer expressions are still intact (no legalization
splitting of `s64`, no register banks), and the existing combiner has already
done its work, so anything the e-graph pass finds is something the greedy
combiner did not. The pass refuses to *rewrite* functions that are already
`Legalized` or `RegBankSelected` (the extracted expression could use
operations that are not legal), but shadow mode works anywhere.

## Source layout

| File | Contents |
|------|----------|
| `include/llvm/CodeGen/GlobalISel/GIEGraph.h`, `lib/CodeGen/GlobalISel/GIEGraph.cpp` | Target-independent e-graph: e-nodes, e-classes, hash-consing, union-find, congruence closure, analyses, refinement edges, pattern parser and matcher, saturation, extraction, cost model. Depends only on `Support` and `LLT`. |
| `lib/CodeGen/GlobalISel/GIEGraphRules.cpp` | The rule library: rules generated from operator properties plus the hand-written cross-operator rules (58 rules). |
| `include/llvm/CodeGen/GlobalISel/GIEGraphCombiner.h`, `lib/CodeGen/GlobalISel/GIEGraphCombiner.cpp` | The `MachineFunctionPass`: region discovery, MIR -> e-graph, shadow report, MIR re-emission, statistics, timers. |
| `lib/Target/AMDGPU/AMDGPUTargetMachine.cpp` | `-amdgpu-gisel-egraph` pipeline hook. |
| `unittests/CodeGen/GlobalISel/GIEGraphTest.cpp` | Unit tests of the engine and of coverage of existing combines. |
| `test/CodeGen/AMDGPU/GlobalISel/egraph-combiner-*.{mir,ll}` | MIR/llc regression tests. |
| `utils/gisel-egraph/verify_rules.py` | Offline Z3 proof of every rule's bitvector identity. |

## Data structures

### ENode

```cpp
struct ENode {
  ENodeKind Kind;     // Input | Constant | Operation
  unsigned Opcode;    // TargetOpcode::G_* (G_CONSTANT for constants)
  uint32_t Flags;     // nuw / nsw / exact / disjoint (MachineInstr::MIFlag)
  LLT Ty;             // result type
  unsigned InputIdx;  // for inputs
  APInt Imm;          // for constants, width == Ty.getSizeInBits()
  SmallVector<EClassId, 2> Ops;
};
```

* Opcodes are the real `G_*` opcodes; there is no parallel enumeration.
* Types are real `LLT`s. Merging two classes of different types, or
  instantiating a rule whose variables do not have the required types, is
  rejected.
* Flags are part of the node identity, so `add nsw a, b` and `add a, b` are
  different operators and never hash-cons together.
* An *input* is an opaque, typed symbolic value with an index. The pass maps
  every distinct virtual register used by (but not defined in) the region to
  exactly one input, so repeated uses of the same SSA value are the same leaf,
  and different registers are never assumed equal.

### EClass

```cpp
struct EClass {
  LLT Ty;
  SmallVector<ENode, 2> Nodes;
  SmallVector<EClassId, 1> RefinesTo;   // refinement edges (see below)
  std::optional<APInt> Const;           // analysis: known constant
  bool NotUndef, NotPoison;             // analysis: definedness
};
```

### EGraph

* `add()` canonicalizes operands with `find()` and hash-conses through an
  `unordered_map<ENode, EClassId>`; inserting an existing node returns its
  class.
* **Commutativity is canonicalization, not a rule.** `canonicalize()` orders
  the two operand classes of a commutative operator by id, so `a + b` and
  `b + a` are the same e-node as soon as they are inserted, with no
  saturation step. `rebuild()` re-canonicalizes after merges, which re-sorts
  operands whose ids changed (so `a + b` and `b + c` become congruent once
  `a == c`). Since only one order is stored, the matcher tries both operand
  orders of a commutative node. Flags stay on the node: `nsw`, `nuw` and
  `disjoint` are symmetric in the operands, so a flagged commutative node
  can be reordered too. Emission puts a constant operand on the right
  (GlobalISel's canonical form) instead of following the id order.
* `merge()` is union-by-size with deterministic tie breaking; it joins the
  analyses and marks the graph dirty.
* `rebuild()` restores the congruence invariant: it re-canonicalizes every
  node, re-hash-conses them, merges classes that now contain the same
  canonical node, and repeats until no merge happens. This is the simple
  "rebuild from scratch" form of congruence closure rather than egg's
  incremental parent-list repair; it is O(nodes) per round and adequate for
  regions bounded at 5000 nodes. After congruence it canonicalizes refinement
  edges and recomputes the analyses to a fixpoint.
* After the analyses, classes with a known constant are *pruned* to their
  constant leaf (as egg's constant-folding analysis does). The removed nodes
  stay in the hash-cons memo and still take part in congruence closure, so
  re-deriving one is a no-op rather than a new class. Without pruning, once
  `a == a + 0` the class of `0` collects `0 + 0`, `0 * 2`, `0 << 1`, ... and
  the factoring and folding rules keep minting new constants; three-instruction
  regions then exhausted the 5000-node budget.
* The graph is never mutated during matching (read phase), only during the
  write phase, followed by one `rebuild()` per iteration (egg-style deferred
  rebuilding).

## Semantics: equivalence vs. refinement

LLVM integer values can be `undef` (each *use* may observe a different value)
or `poison`. Many identities that hold for bitvectors are therefore only
*refinements* in LLVM: `x - x -> 0` is a valid transformation, but `x - x` and
`0` are not interchangeable, because the reverse direction would turn a
defined `0` into something that may be undef/poison.

An e-graph merge asserts *interchangeability in both directions*: after
merging, extraction may pick any member for any use of the class. Merging on a
one-way refinement is therefore unsound. The PoC keeps two relations:

1. **Equality** (union-find + congruence) — only for proven equivalences.
2. **Refinement edges** `C ~> D` — "any use of C may be replaced by D". These
   are never used to merge. Extraction may follow them (taking `D` for `C`);
   matching may look *through* them below the root of a pattern, but then the
   result is itself only a refinement (refinement is monotone in every LLVM
   integer operation and transitive, so compositions stay sound).

This is option B of the task description restricted to a small, checkable
semantic model, combined with option A (definedness analyses) to upgrade
refinements to equivalences when inputs are known to be defined.

### Which matches are equivalences?

A rule is a bitvector identity `L(v1..vn) == R(v1..vn)` that holds for all
assignments (proved with Z3 for widths 1/2/3/8/16/32/64, see
`utils/gisel-egraph/verify_rules.py`). All pattern operators are the
*unflagged* `G_ADD/SUB/MUL/AND/OR/XOR` and `G_SHL/LSHR/ASHR` with a constant
in-range amount. These operators produce poison iff an operand is poison and
never create undef from defined operands.

For a match with variables bound to classes, let `occL(v)` / `occR(v)` be the
number of occurrences of `v` in each pattern. The code
(`RewriteRule::isExactFor`) treats the match as an **exact equivalence** iff
for every variable `v`:

* if `occR(v) == 0` (dropped): `v` is not poison, and if `occL(v) > 1` also
  not undef;
* otherwise, if not `occL(v) == occR(v) == 1`: `v` is not undef.

Argument: poison — both sides are poison iff some mentioned variable is
poison; if a variable is dropped, the LHS can be poison while the RHS is not,
unless the variable is known not poison. Undef — model each *occurrence* of an
undef-carrying value as an independent draw. If each variable occurs exactly
once on each side, the identity holds for every combination of draws, so both
sides have the same set of possible values. If a variable occurs several
times, the identity is only guaranteed on the "diagonal" (equal draws), so the
sets may differ unless the value is known not undef.

The match is a **refinement** (`RewriteRule::isRefinementFor`) iff every
variable occurs at most once on the RHS or is not undef: the RHS variables are
a subset of the LHS variables (checked when parsing the rule), so RHS poison
implies LHS poison; and using a variable at most once on the RHS picks a point
on the LHS' diagonal. If neither holds, the match is rejected and counted as
`unsafe`.

Further rules that make a match a refinement only:

* any structural part of the LHS was matched through a refinement edge;
* the matched node carries a poison-generating flag. A flagged operation is
  refined by the same operation without the flag (the flag only adds
  poison), so `sub (add nsw a, b), b ~> a` is allowed, but `add nsw a, b` is
  never merged with `add a, b`.

### Definedness analyses

`NotUndef` / `NotPoison` are e-class analyses joined with OR over the members
(all members of a class are exactly equal, so one defined member suffices):

* constants are defined;
* inputs are defined if their definition is `G_FREEZE` or `G_CONSTANT`
  (deliberately conservative: function arguments, loads and `COPY`s from
  physical registers are treated as possibly undef and poison; the generic
  `isGuaranteedNotToBeUndefOrPoison` helpers are not used because they recurse
  into `COPY`s of physical registers);
* `G_IMPLICIT_DEF` is possibly undef;
* an operation is not undef if its operands are not undef; it is not poison if
  it is unflagged, its operands are not poison and (for shifts) the amount is
  a constant in range.

Consequently, on ordinary code most cancellation and factoring results are
refinements; with frozen inputs they become equivalences (see the
`frozen` case in `egraph-combiner-shadow.mir`).

### Other semantic restrictions

* Shifts are rewritten only when the amount is a constant smaller than the
  width; constant folding never folds an out-of-range shift (it is poison).
  Right-hand sides that would create such a shift are rejected.
* Shift amount types may differ from the value type (`G_SHL s64, s32`); a
  constant amount is re-materialized at the value width only if it fits.
* Only scalar types are supported (any width up to 128). Vectors, pointers,
  floating point, memory, PHIs, multi-def instructions and anything with
  implicit operands are region boundaries.
* Regions never cross basic blocks.

## Rewrite rules

### Operator properties

The generic part of the library is not written rule by rule. Each supported
operator has an `OpProperties` entry (`getAllOpProperties()` in
`GIEGraph.cpp`), and `GIEGraphRules.cpp` derives the rules from it:

| Property | Meaning | Generated rules |
|----------|---------|-----------------|
| `Commutative` | `a op b == b op a` | none; enforced by canonicalization (above) |
| `Associative` | `(a op b) op c == a op (b op c)` | `op-assoc-r`, `op-assoc-l` |
| `RightIdentity` `e` | `a op e == a` | `op-zero`, `op-one`, `op-ones` |
| `RightAbsorbing` `z` | `a op z == z` | `mul-zero`, `and-zero`, `or-ones` |
| `Idempotent` | `a op a == a` | `and-self`, `or-self` |
| `SelfValue` `c` | `a op a == c` | `sub-self`, `xor-self` |
| `DistributesOver` `I` | `a op (b I c) == (a op b) I (a op c)` | `factor-op-I` (factoring direction only); with an identity `e` also `factor-op-I-id`: `(a op b) I a => a op (b I e)`, plus `-id-l` if `I` is not commutative |
| `RightDistributesOverConst` `I` | `(a I b) op #k == (a op #k) I (b op #k)` | `factor-shl-add` (the shared amount must be a constant) |
| `Fold` | constant evaluation (returns no value for poison) | `fold-op` |
| `IsShift` | second operand is a shift amount | matcher/analysis restrictions |

The current table:

| Operator | Comm. | Assoc. | Identity | Absorbing | Self | Distributes over |
|----------|:-----:|:------:|---------:|----------:|------|------------------|
| `G_ADD` | yes | yes | 0 | | | |
| `G_SUB` | | | 0 | | `a - a == 0` | |
| `G_MUL` | yes | yes | 1 | 0 | | `G_ADD` |
| `G_AND` | yes | yes | -1 | 0 | idempotent | `G_OR`, `G_XOR` |
| `G_OR` | yes | yes | 0 | -1 | idempotent | `G_AND` |
| `G_XOR` | yes | yes | 0 | | `a ^ a == 0` | |
| `G_SHL` | | | 0 | | | `G_ADD` (shared constant amount) |
| `G_LSHR`, `G_ASHR` | | | 0 | | | |

Being in the table is also what makes an operator supported (the pass's
region discovery, the poison analysis, the pattern parser). Supporting a new
operator, or recording a new fact about an existing one, is therefore one
table entry. The entry is checked like any rule:
`-gisel-egraph-print-rules` prints every generated rule and every property
that is enforced implicitly (commutativity), and `verify_rules.py` proves
all of them with Z3 using its own, independent operator semantics. A wrong
property such as "`G_SUB` is commutative" fails there.

### Hand-written rules

Rules that relate *different* operators stay hand-written in
`GIEGraphRules.cpp`, for example:

```cpp
Add("add-self", "(G_ADD ?a ?a)", "(G_MUL ?a 2)");
Add("mul-pow2-to-shl", "(G_MUL ?a #c)", "(G_SHL ?a $0)",
    [](const EGraph &G, const RuleMatch &M, Computed &Out) {
      ... precondition on #c, compute $0 = log2(#c) ...
    });
```

`?x` binds an e-class, `#c` binds a known constant, integer literals are
sign-extended or truncated to the width (`-1` is all-ones; at `s1` the
literal `1` is also all-ones and `2` is `0`, which is sound because every rule
is a ring or bitwise identity), `$n` is a constant
computed by the optional hook. Whether a match is an equivalence or a
refinement is *derived*, not declared.

| Group | Rules | Typical classification |
|-------|-------|------------------------|
| Associativity (both directions) | `*-assoc-l`, `*-assoc-r` (generated) | equivalence |
| Identities | `add-zero sub-zero mul-one and-ones or-zero xor-zero shl-zero lshr-zero ashr-zero` (generated) | equivalence |
| Absorbing | `mul-zero and-zero or-ones` (generated) | refinement unless operand not poison |
| Idempotence / cancellation | `sub-self and-self or-self xor-self` (generated) | refinement unless defined |
| Negation | `sub-to-add-neg add-neg-to-sub neg-neg neg-sub neg-add add-negs neg-mul mul-neg mul-negconst add-negconst` | equivalence |
| Bitwise not | `xor-ones-to-sub` (`~a == -1 - a`) | equivalence |
| Factoring (one direction only) | `factor-mul-add factor-mul-add-id factor-and-or factor-and-or-id factor-and-xor factor-and-xor-id factor-or-and factor-or-and-id factor-shl-add` (generated), `add-self` | refinement unless the shared operand is not undef (`factor-shl-add` is exact) |
| Strength reduction | `mul-pow2-to-shl shl-to-mul` | equivalence |
| Constant folding | `fold-{add,sub,mul,and,or,xor,shl,lshr,ashr}` (generated) | equivalence |

Distributivity is never applied in the expanding direction, which keeps
growth under control; associativity is bidirectional and, together with the
commuted matching, the main source of growth (bounded by the limits below).

## Saturation

`saturate()` alternates a read phase (collect all matches of all rules, in
rule order and increasing class id) and a write phase (apply matches in that
order), then rebuilds. It stops when an iteration changes nothing (no new
node, class, merge or refinement edge) or a limit is hit.

A backoff scheduler (as in egg) bans a rule that produces more than
`RuleMatchLimit << n` matches in one iteration (default 1000; `n` is the
number of earlier bans) for `RuleBanLength << n` iterations (default 2) and
drops its matches. A graph with banned rules is never reported as saturated.
In practice this throttles associativity and commutativity: on
`~(a + -1)` it cut the graph from 4599 to 290 nodes with the same result.


| Option | Default | Meaning |
|--------|---------|---------|
| `-gisel-egraph-max-region-instrs` | 32 | region size cap during discovery |
| `-gisel-egraph-max-nodes` | 5000 | stop applying matches when reached |
| `-gisel-egraph-max-iterations` | 10 | saturation iterations |
| `-gisel-egraph-max-matches` | 20000 | matches collected per iteration |

The budget trades compile time for depth; see
`GIEGraphCombiner-Evaluation.md` for measurements. Cancellation chains such
as `(a - b) + (b - c) + (c - a)` need about 9 iterations and about 900 nodes.

Everything is deterministic: classes are visited in id order, nodes in
insertion order, hash maps are only used for lookup, never iterated.

## Extraction and cost model

`Extractor` computes, by a Bellman-Ford style fixpoint, the minimum *tree*
cost of every class: `cost(n) = nodeCost(n) + sum(cost(child))`, and
`cost(C) = min(min over nodes, min over refinement targets)`. Operations cost
at least 1 and refinement edges are only followed when *strictly* cheaper, so
the chosen solution is acyclic (proof sketch in the source).

Profitability uses the *DAG* cost of the chosen solution for all roots of the
region (each class counted once) against the cost of the original
instructions. Choosing by tree cost and judging by DAG cost is a known
approximation: shared subexpressions may be double counted when choosing.
For multi-root regions the roots are extracted with the same choice table,
which shares classes but is not a global optimum.

`DefaultCostModel` (configurable, virtual `CostModel` base for targets):

| Node | Cost |
|------|------|
| `G_CONSTANT` | `-gisel-egraph-constant-cost` (0) |
| input | 0 |
| add/sub/and/or/xor/shifts | 1 |
| `G_MUL` | `-gisel-egraph-mul-cost` (2) |
| width scaling | x ceil(width / 32) |

These are crude instruction-count proxies, not AMDGPU latencies. On AMDGPU a
32-bit `v_mul_lo_u32` is a quarter-rate instruction and a 64-bit multiply
expands to several instructions; constants are free if they are inline
constants. A target cost model would consider these as well as register
banks, VOP2/VOP3 encodings and legalization expansion.

## MIR integration

### Region discovery

Per basic block, in instruction order, a *candidate* is a supported opcode
with exactly three virtual register operands, a scalar type of at most 128
bits and no flags other than nuw/nsw/exact/disjoint. A region is a connected
component (through def-use edges between candidates of the same block) grown
by worklist up to the size cap. Operand registers defined by `G_CONSTANT`
become constant nodes; all other non-region operands become inputs.

A region instruction is a **root** if it has any non-debug use outside the
region (other instructions, other blocks, PHIs). All values needed outside the
region are therefore roots, and internal values have only internal users. A
value with several in-region users is shared in the e-graph through
hash-consing; one with an external user is a root and stays available.

### Rewrite

In rewrite mode, a region is re-emitted iff

1. the extracted DAG cost is strictly smaller than the original cost,
2. a dry run over the chosen DAG (in emission order) finds no cycle and every
   input it uses is defined before the insertion point of the root that first
   needs it (inputs from other blocks dominate the whole block),
3. no root or input register carries a register class or bank.

Emission happens only after all checks pass (all-or-nothing). Each root's
expression is emitted with `MachineIRBuilder` immediately before the original
root instruction, reusing classes already materialized for earlier roots and
re-materializing constants locally. Then every root register is replaced with
`MRI.replaceRegWith`, and the old region instructions are erased in reverse
order (debug users are salvaged or marked undef). Constants that become dead
are erased; other dead inputs are left to later dead-code elimination. If any
check fails, the MIR is not touched.

### Shadow mode and reporting

Shadow mode runs steps up to extraction and validation and never modifies the
function (`egraph-combiner-shadow.mir` diffs the output against
`-run-pass=none`). `-gisel-egraph-report` prints one line per region with node
counts, saturation status, merges/refinements/unsafe matches, old/new cost,
whether the candidate is an equivalence or a refinement, the extracted
expression for each root, and the number of applications per rule.

Statistics (`-stats`, `DEBUG_TYPE=gisel-egraph`) cover regions, nodes before
and after saturation, classes, matches, merges, refinements, unsafe matches,
iterations, saturated vs. budget-limited regions, profitable candidates,
applied rewrites and estimated cost saved. `-time-passes` adds
`build`/`saturate`/`extract` timers in the `gisel-egraph` group.

## Known limitations

* Regions are single-block, scalar-integer only, and capped at 32
  instructions; larger connected components are split by the cap.
* Inputs are almost never provably defined in real code, so most profitable
  candidates are refinements. They are still sound to apply.
* Congruence closure rebuilds from scratch each iteration, and every rule is
  matched against every class in every iteration (no incremental matching).
  Saturation is 98-99% of the pass time.
* Tree-cost extraction, DAG-cost profitability; no ILP or global sharing
  optimization, no critical-path or register-pressure awareness.
* The cost model is generic; legality is not consulted (rewrites are only
  done pre-legalization, where the AMDGPU legalizer accepts all supported
  scalar operations).
* Emitted instructions are not re-visited, and the pass does not run the
  existing combiner afterwards; e.g. `x * 8` is extracted as `x << 3` only
  because `shl` is cheaper in the cost model.
* AC rules make the graph grow quickly on long chains (> ~8 operands); the
  backoff scheduler and the node budget bound this, and such regions only get
  the rewrites found so far.
* Pruned constant classes cannot be matched structurally, so a rule that
  needs the negation of a constant must have a constant form (this is why
  `add-negconst` exists next to `add-neg-to-sub`).
* Missing rules found in the evaluation: `x | ~x -> -1`, `x & ~x -> 0`.

## Future work

* **TableGen front end.** The S-expression rules map naturally onto
  `GICombinePatFrag`-style DAGs:

  ```tablegen
  def AddAssoc : GIEGraphRule<
    (G_ADD (G_ADD $a, $b), $c),
    (G_ADD $a, (G_ADD $b, $c))>;
  def MulPow2 : GIEGraphRule<
    (G_MUL $a, $c:CImm),
    (G_SHL $a, (log2 $c)),
    [IsPow2<"c">]>;
  ```

  Exactness would continue to be derived from occurrence counts, so a rule
  author only states the identity and constant preconditions; the emitter
  could also emit the Z3 obligation.
* **Target cost models** (AMDGPU: quarter-rate multiplies, 64-bit expansion,
  inline constants, SGPR vs. VGPR) and legality-aware extraction for running
  after the legalizer.
* **Incremental rebuild and matching** (egg parent lists, matching only
  classes touched since the last iteration) for compile time.
* **Better definedness**: use known-bits / `!noundef` information carried
  from IR, so more candidates become exact equivalences.
* **Automatic rule discovery** à la Ruler/Souper: enumerate small terms over
  the `G_*` operators, cluster by fingerprinting, prove candidates with Z3
  offline (the existing `verify_rules.py` is the checking half), and add the
  verified rules to the library. Compilation itself never needs a solver.
