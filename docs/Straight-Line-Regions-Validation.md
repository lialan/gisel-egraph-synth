# Straight-line region integration validation

Validated on nod on 2026-11-12, after rebasing the implementation onto main
`4cb0a0b` (integer/FP condition synthesis). LLVM is pinned at
`37a1706d0eac1774701a0a44d9fb4fa542f56fde`. A subsequent documentation-only
main update (`c16a147`) was integrated before landing; all executable sources,
rule data and target profiles remained identical to the tested tree.

- Full Python suite: 624 passed, including the opt-in build and execution of
  automatically discovered cross-block rules on AMDGPU and AArch64.
- C++ unit tests: 175 passed.
- MIR lit: 11/12 passed. The existing `AMDGPU/egraph-combiner-vector.mir`
  failure has the same three checks as the independently reproduced baseline
  failure documented in `IntegerFP-Conversion-Validation.md`.
- Existing catalog: all 128 rules re-proved with Z3 5.4.1.
- Default `emit --check`: passed.
- `git diff --check`: passed.

The rebase retained both the FP value-facts contract and the straight-line
region contract in the semantic fingerprint. The catalog and both target
profile fingerprints were refreshed after proving that every rule revision,
selected rule, and selection order is unchanged. Neither profile selects a
region rule. Both default generated files are byte-for-byte identical to
main's files; this refresh enables the existing defaults without promoting
new rules or claiming new target performance measurements. Older external
catalogs and caches still require revalidation.

The cross-block add/carry and subtract/borrow examples test extraction,
search, joint proof, generated code, dominance, and unchanged CFG. The
add/carry algebraic pattern already exists in upstream CodeGenPrepare;
these examples do not establish extra benefit over the full upstream
pipeline. The separate online e-graph combiner remains block-local.

Full integration logs and end-to-end MIR artifacts are in
`/home/nod/gisel-straight-line-regions-20261112/build/validation/landing/`.
