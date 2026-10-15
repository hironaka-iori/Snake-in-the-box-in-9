# Three-center pattern(2,2,3)

Checkpoint: 16 October 2026.

Both radius-three encodings are solver-infeasible and their proofs replay in Python. Radius two is feasible. The two large Lean certificate builds exhausted memory; no geometric exclusion or 244 bound is claimed.

Sources and evidence: scripts/; data/; lean/; logs/

Paths beginning with `work/`, `outputs/`, or `paper/` are relative to the repository root. Shared proof projects and historical machine data keep stable paths; this folder holds the milestone narrative and new dedicated work.

## Reproduction

Run from the repository root, with Lean 4.19.0 on PATH:

```sh
python milestones/07-window-223/scripts/audit_window_encoding.py
python milestones/07-window-223/scripts/export_rup_terms.py --prefix milestones/07-window-223/data/window_223_repeated_compact --module Window223RepeatedCertificate --structured --output-dir milestones/07-window-223/lean
python milestones/07-window-223/scripts/split_rup_proof.py --source milestones/07-window-223/lean/Window223RepeatedCertificate.lean --core milestones/07-window-223/data/window_223_repeated_compact_core.json --output-dir milestones/07-window-223/lean/generated/repeated --chunk-size 40 --check
```

The sequential split build is running; partial progress is not a certificate. Its manifest lives beside the generated modules. The distinct-coordinate case remains unverified. The source exporter and splitter are untrusted; every emitted theorem must pass Lean.
