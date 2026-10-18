# Three-center pattern (2,2,3)

Completed: 18 October 2026. **Lean-proved global interval: 191 <= a(9) <= 244.**

Both radius-three window shapes are unconditionally excluded, including their
geometric semantic bridges, alpha-preserving normalization, and path reversal.
The retained cores contain 1,588 / 2,728 input clauses and 2,327 / 18,461 RUP
steps. These are distinct from the original LRAT lengths 3,744 / 24,895.
The original single-file and early split attempts are historical artifacts.

The maintained implementation is [`work/window244`](../../work/window244/PLAN.md).
Its small modules passed an isolated source-only reconstruction of 8,229 modules.
The final four theorem audits use only `propext`, `Classical.choice`, `Quot.sound`.
No solver output is assumed as an axiom. No KEEP bank evidence was modified.

## Reproduction

From the repository root, with Lean 4.19.0 on PATH and the pinned mathlib checkout:

```sh
python work/window244/audit_encoding.py
python work/window244/check_sequence_bounds.py
python work/spectral/verify_strengthened.py --window244 --mathlib-dir /path/to/mathlib
```

Use `--resume-build` with an existing window244 build directory after interruption.
Generated Lean modules are recreated from the preserved core inputs and generators;
each generated source and output hash is recorded in the build manifest.

Final [manifest](../../outputs/window244/final-reproduction-manifest.json),
[axiom audit](../../outputs/window244/FinalAudit.log),
[summary](../../outputs/window244/final-verification.json), and
[Chinese report](../../work/window244/REPORT.zh-CN.md).
Exact optimality remains unresolved. Any further upper bound needs additional proofs.
