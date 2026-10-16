# Paused regrowth certificate experiments

This directory records incomplete experiments as of 16 October 2026. The
authoritative scope description is
`milestones/08-exhaustive-search/lean_completion.md`.

No complete KEEP=112 exclusion is established here. The first Boolean proof
was paused after 35 of 150 modules compiled. Its geometric interpretation and
the remaining bank entries still require formal proofs. The manifests mark
this explicitly as `PAUSED_BY_USER`; the `before-pause` copies preserve the
original running records.

The best current Boolean experiment uses `totalizer112_82.cnf`,
`totalizer_plain.json`, `totalizer_plain.lrat` and
`totalizer_plain_core.json`. It has 1,547 retained input clauses and 5,902
derived clauses. `sat-export/` contains the exported proof, while
`sat-first-checked/` contains its split source and available checking logs.
Generated proof text is not itself evidence that the final theorem compiled.

From the repository root, with Python 3.12 or later and Lean 4.19.0 on PATH:

```sh
python milestones/07-window-223/scripts/export_rup_terms.py --prefix work/lean/totalizer_plain --module Dfs112FirstBoolean --structured --output-dir work/lean/sat-export
python milestones/07-window-223/scripts/split_rup_proof.py --source work/lean/sat-export/Dfs112FirstBoolean.lean --core work/lean/totalizer_plain_core.json --output-dir work/lean/sat-first-checked --chunk-size 40 --check
```

The remaining files preserve alternative encodings, timing probes and solver
outputs for comparison. They do not establish formal exclusions. `DfsFast.lean`
is an experimental optimization that showed no useful speed improvement and
is not part of the maintained certificate pipeline. The general encoder
`work/build_regrowth_cnf.py` has additional provenance information; its output
must be compared with the experimental formula before reusing a certificate.

Build caches, downloaded toolchains and the local checkpoint archive are not
included in this branch. No checks are scheduled or running at this checkpoint.
