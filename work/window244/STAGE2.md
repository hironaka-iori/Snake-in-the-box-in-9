# Stage 2: independent census and minimal forbidden sets

Stage 1 passed: `outputs/window244/final-verification.json`, unconditional 244.
No bound 243/242 is claimed. Keep the completed Stage-1 Lean sources and data fixed.

**18 October update:** upstream branch `research/unconditional-241` now supplies
an unconditional 241 theorem and passing audit log. The duplicate local 242 case
checks were stopped with all valid checkpoints retained. The active task is
the independent source-only review described in `UPSTREAM_REVIEW.md`; do not
restart the superseded coordinator while that review is running. The running
descriptions below record the preceding development checkpoint.

## Completed independent census and subset calculation

`survey_stage2.py` completed all 48 radius-three cases with OR-Tools 9.15.6755,
one worker, seed 41 and a total 120-second budget per case. No UNKNOWN occurred.
The original 12 both-shapes-infeasible patterns were all reproduced. Exhaustive
canonical enumeration gives 24 rather than 23 patterns: the omitted `(1,7,1)`
also proved infeasible in both local models, yielding 13 such canonical patterns.
All these new exclusions remain **SOLVER_ONLY** until their Lean chains pass.

`minimal_patterns.py` searched every candidate subset through cardinality five,
with an independent exhaustive short-sequence check. In this sequence relaxation
and this candidate universe, the smallest extra sets are:

- Bound 243: `{232,414}` or `{323,414}` (two additional patterns).
- Bound 242: `{141,142,224,232,323}`, `{141,224,232,323,414}`, or
  `{151,224,232,323,414}` (five additional patterns).

Reversals are included. The chosen certification set is
`{232,414,141,224,323}`, to reuse the 243 subtarget. Counts larger than seven are
compressed to eight/even or nine/odd, never to four/five. Forbidden triples apply
only to internal vertices, excluding the two endpoints. This matters for 414.
The DP reproduces baseline 244 and all-candidate 242; it proves no new Lean bound.

## Proof-producing solves completed; Lean checks running

`stage2_certificates.py` ran CaDiCaL 2.1.2 with LRAT logging, seed 41, one thread,
and an external 120-second wall limit. All ten chosen shape instances are UNSAT
and passed deletion-aware independent replay and separate backward RUP trimming.
The Windows executable rejects POSIX `-t`; that failed command is archived in
`certificates-cli-flag-failed/`, and no exclusion was inferred from it.

`build_stage2.py` now checks the generated Boolean proofs and concrete geometric
instances with two independent case workers, 1,800 MiB per Lean process and
per-module source/import/output/log hashes. It uses the verified Stage-1 source
build only as a development foundation cache. No new arbitrary-window exclusion
or stronger global bound follows merely from these development checks.

Live state: `outputs/window244/stage2/lean-build.json` and `<case>-lean.json`;
logs: `stage2-lean.stdout.log` / `stage2-lean.stderr.log` in `outputs/window244/`,
and per-module `stage2/lean-logs/`. Do not duplicate the running coordinator.
For failures, inspect the case manifest and exact log, split or repair as needed,
then resume with the same arguments after the lock is free.

```
python work/window244/survey_stage2.py --solver-packages /path/to/ortools/packages
python work/window244/minimal_patterns.py
python work/window244/stage2_certificates.py --solver /path/to/cadical
python work/window244/build_stage2.py --foundation /path/to/successful/window244-build --mathlib-dir /path/to/mathlib --lean-bin /path/to/lean-4.19.0/bin --jobs 2
```

Census and solver code/model hashes, parameters, logs, status and elapsed time are
saved per invocation. Completed raw inputs are archived as
`outputs/window244/stage2-evidence.tar.gz`, with an inventory in
`stage2-evidence-inventory.json`. Extract with
`tar -xzf outputs/window244/stage2-evidence.tar.gz -C outputs/window244`.
The archived inputs are untrusted until their emitted proofs pass the kernel.

## Subsequent obligations

1. Preserve the completed census and minimum-subset evidence described above.
2. Preserve or independently cross-check the minimum extra forbidden-pattern sets for bounds 243 and 242,
   including reversals and the already proved 222/223/322 restrictions.
   **Do not reuse the Stage-1 alpha truncation to 4/5:** newly forbidden patterns
   involving 4 or 5 can invalidate it. Use the true alpha range or justify a new
   compression above every forbidden entry, preserving parity and constraints.
3. Certify only necessary new patterns: explicit CNF, proof-logging solver,
   independent replay, generic semantic bridge, kernel checks and normalization.
4. Prove the stronger potential and aggregate consequence in Lean, with fresh
   source reconstruction and final axiom audit before reporting a better bound.
5. Do not extend radius for 233/242/324; new progress there needs a justified
   longer-window model or new invariant. No KEEP backpropagation work.

Only 244 is currently proved. Stop and report the original invalid-clause,
irreducible-memory, missing-shape, or three-working-day stagnation conditions.
