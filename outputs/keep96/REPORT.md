# KEEP=96 feasibility report

Baseline `acee575f181b8a6d35775f985169ec15cb2cf021`; independent branch `research/keep96-feasibility`. All new work is in
`work/keep96/` and `outputs/keep96/`. KEEP=112 sources/results remain unchanged.

## What was established

The bank has 131 valid 191-edge induced paths, 262 oriented entries. All 262 known
witnesses satisfy the KEEP=96 encoding at their correct 192-vertex total, including
every auxiliary counter assignment. All fail as assignments to the 193-vertex
target, as expected. This is a positive-control/data audit, not a universal proof
of encoder soundness. The mathematical interpretation is explained in the README.

The 12 outcome-blind, structurally varied pilot cases returned **{'UNSAT': 12}** with a
300-second worker cap and a hard 2048 MiB memory cap. Runtime range:
0.214–221.701 seconds; median 0.416 seconds;
sum 500.015 seconds. 8 UNSAT cases finished below ten seconds.

This justified a single **10-second** screen of the other 250 entries, under the
same memory limit. Only the computation budget changed: KEEP=96 and the 193-vertex
target did not. Combined outcomes: **{'UNSAT': 242, 'UNKNOWN': 20}**. The complete table is
`results.csv` / `results.json`; each row includes its budget and evidence paths.
Unknown entries: `[5, 9, 15, 21, 23, 25, 26, 27, 29, 30, 31, 36, 41, 121, 125, 143, 254, 255, 259, 260]`. They were not repeatedly retried or called SAT/UNSAT.

## Evidence and limitations

All 262 compressed DIMACS formulas match their saved JSON mappings, counter trees
and clause provenance. Hashes of formulas, configurations, models/proofs and logs
were verified. There are 166 distinct DIMACS byte streams.
Solver: Glucose 4.1 via python-sat 1.9.dev16, default parameters, proof logging on;
the binary hash and environment are in each result. Solver times are not portable
benchmarks: bounded certificate checks ran concurrently for part of the survey.
The parent's 0.1-second polling may cause small wall-limit overshoot.

Proof-check statuses: `{'NOT_CHECKED': 238, 'PASSED_EXECUTABLE_RUP_CHECK': 21, 'UNKNOWN_TIMEOUT': 3}`. These refer to executable
RUP checking, not Lean. A failed/timed-out proof check does not upgrade the solver
result to a verified theorem. All available UNSAT certificates remain locally
preserved. `certificate-index.json` records paths, sizes and SHA256 hashes, including
large proofs omitted from Git. To restore those on another computer, transfer them
from this clone or rerun the exact recorded configuration; missing evidence is
never silently reused. The largest pilot proof is about 55.4 MiB compressed and
contains over three million proof lines, demonstrating a certification bottleneck.

No SAT result is automatically a snake: the relaxation allows a head path plus
disconnected cycles. The worker validates any SAT model, reconstructs its head
component, and checks all unordered vertex pairs before calling it a genuine
192-edge construction. No global optimality conclusion follows from bank prefixes.

## Recommendation

KEEP=96 is computationally promising for many instances, but a full KEEP=96 Lean
campaign is **premature**. First resolve the remaining UNKNOWN cases with separately
budgeted, justified experiments; do not silently increase this survey's limits.
Second, use an efficient native proof checker and proof trimming/compression before
translating multi-million-line proofs into Lean. Third, establish the KEEP=96
geometric interpretation/coverage bridge for the exact encoder used here. Exact
formula deduplication may reduce repeated Boolean work, but must not erase the
distinct bank-prefix interpretations. No KEEP=112 worker or Lean campaign was run.

## Reproduction and resumption

See `work/keep96/README.md`. Run `prepare.py`, `run.py --phase pilot`, then
`screen_remaining.py`; all solver attempts are bounded and persisted per entry.
The second pilot invocation reused all 12 completed attempts after checking the
formula/configuration identity and saved hashes, without new solver calls.
Run `finalize.py` only once both phases finish. A `started.json` without a result is
an incomplete attempt, never a completed proof. Full proof locations remain local
even when the appropriately sized Git evidence subset is used elsewhere.
