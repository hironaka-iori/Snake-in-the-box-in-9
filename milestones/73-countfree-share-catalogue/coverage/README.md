# Six-transition shape coverage

Checkpoint: 2 November 2026. Status: **Lean-checked**. This directory proves finite catalogue coverage and its application to the canonical direction list of an arbitrary snake window.

Let \(R\) consist of these nine direction patterns:

```
012031 012032 012034 012301 012304
012310 012314 012340 012345
```

For every canonical restricted-growth direction list \(c\) of length six satisfying the induced-path parity condition,

\[
c\in R\quad\text{or}\quad\operatorname{canon}(\operatorname{reverse}(c))\in R.
\]

`canonical_coverage` proves this statement. Its finite certificate is `restricted_growth_table`, evaluated by Lean's kernel using the existing complete restricted-growth enumerator. That enumeration has 203 words; an independent Python cross-check recovers the saved 12 induced orientations. No enumeration of all concrete coordinate assignments is used.

`snake_window_coverage` applies the result to every actual six-transition window of every `Snake m`, with start \(r\) satisfying \(r+6\le m\). It proves that the canonical actual direction block, or the canonical reverse of that actual block, lies in \(R\). The theorem uses the established `snake_inducedPattern_block`, `canon_isRGS`, `length_canon`, `inducedPattern_canon`, and `canon_canon_drop_reverse` lemmas.

The four printed theorems are in `lean/SixShapeCoverage.lean`. They use only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. `data/proof-audit.json` records the successful source-matched build, compiled artifact hash, catalogue correspondence, and printed axioms.

## Reproduction and provenance

Run `scripts/prepare_support.py`, `scripts/check.py`, then `scripts/audit.py` with the repository's configured Python runtime. The build uses Lean 4.19.0 and one Lean process.

Five existing normalization modules are copied to `upstream/` for source preservation. Their sources match both milestone 32's pinned normalization-support receipt and the current maintained sources after line-ending normalization. Existing compiled modules are reused; their hashes and original log hashes are recorded in `data/support.json`. This is not a fresh rebuild of the entire inherited cube and normalization dependency tree.

## Scope

Coverage is now a theorem about arbitrary snake direction blocks. The proof does not supply the coordinate-name adapters dispatching the nine local share inequalities, and it does not build the larger nine-transition/history graph walk. It establishes no new numerical upper bound by itself.
