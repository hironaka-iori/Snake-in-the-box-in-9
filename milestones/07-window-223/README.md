# Three-center pattern(2,2,3)

Checkpoint: 16 October 2026.

Both radius-three encodings are solver-infeasible and their proofs replay in Python. Radius two is feasible. The repeated-coordinate Boolean contradiction has passed Lean in 61 sequential modules. The distinct-coordinate build is in progress. No complete geometric exclusion or 244 bound is claimed.

Sources and evidence: scripts/; data/; lean/; logs/

Paths beginning with `work/`, `outputs/`, or `paper/` are relative to the repository root. Shared proof projects and historical machine data keep stable paths; this folder holds the milestone narrative and new dedicated work.

## Reproduction

Run from the repository root, with Lean 4.19.0 on PATH:

```sh
python milestones/07-window-223/scripts/audit_window_encoding.py
python milestones/07-window-223/scripts/export_rup_terms.py --prefix milestones/07-window-223/data/window_223_repeated_compact --module Window223RepeatedCertificate --structured --output-dir milestones/07-window-223/lean
python milestones/07-window-223/scripts/split_rup_proof.py --source milestones/07-window-223/lean/Window223RepeatedCertificate.lean --core milestones/07-window-223/data/window_223_repeated_compact_core.json --output-dir milestones/07-window-223/lean/generated/repeated --chunk-size 40 --check
```

The completed repeated-coordinate receipt is `data/repeated-lean-manifest.json`; it records all 61 successful modules and the final standard-axiom audit. The distinct-coordinate build has 464 modules; partial progress is not a certificate. Its live manifest lives beside the generated modules. The source exporter and splitter are untrusted; every emitted theorem must pass Lean.

## Geometric interpretation

- `lean/WindowGeometry.lean` proves positive degree for a nontrivial snake and the endpoint-prefix counter rules from the two-endpoint bound.
- `lean/WindowCycles.lean` checks all 112 distinct retained cycles and excludes their complete selection by an induced path.
- `lean/WindowCornerData.lean` proves the 21-pair enumeration, checks the four corner configurations, and proves that the complete threshold-counter system is satisfiable exactly at the intended missing count.
- `lean/WindowSingletons.lean` identifies missing eligible corners with the actual singleton-square count. It verifies the ordered corner lists and proves that an actual snake supplies the counter assignment at each normalized center.

To rebuild these support modules, first reproduce the strengthened bound as documented in milestone 05. Then run, from the repository root:

```sh
python milestones/07-window-223/scripts/verify_window_support.py --mathlib PATH_TO_PINNED_MATHLIB --dependency-build PATH_TO_COMPLETED_STRENGTHENED_BUILD
```

This reuses the checked upstream dependencies, verifies their Lean source hashes, and recompiles the five support modules, including the shared cycle lemma. Its result is `data/geometry-support-manifest.json`. It is not a new source-only rebuild of all upstream dependencies.

The remaining obligations are the exact clause-by-clause construction of the imported Boolean constraint records, completion of the distinct-coordinate Boolean proof, and coordinate-permutation normalization for arbitrary windows. The bound remains 245 edges.
