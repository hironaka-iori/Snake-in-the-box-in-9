# Alternative fillings and retained changes

Checkpoint: 20 October 2026. No snake above 191 edges was found.

## Hypothesis and method

An alternative filling of a known snake, possibly after a one-edge retreat, may permit improvement when the free region changes. The prior contracted maximization runs all returned the original selected set.

This experiment fixes expanded length at 191 or 190 and maximizes the number of selected vertices outside the original seed set. It uses the same fixed-outside contraction as milestone 24. A selected set determines an induced path's order up to reversal, so this objective measures an actual change of vertices.

Four Q8 faces are tested: indices 3, 0, 4 and 5 of milestone 23. Each search uses two workers, random seed 193 and a 20-second limit. The two most changed feasible seeds are subsequently repaired in the other three faces, maximizing expanded length with the milestone 24 solver. Those six runs use that solver's random seed 192.

## Outcomes

| Face | Target edges | Status | New selected vertices |
|---|---:|---|---:|
| 3 | 191 | FEASIBLE | 0 |
| 3 | 190 | FEASIBLE | 0 |
| 0 | 191 | FEASIBLE | 0 |
| 0 | 190 | FEASIBLE | 1 |
| 4 | 191 | FEASIBLE | 3 |
| 4 | 190 | FEASIBLE | 4 |
| 5 | 191 | FEASIBLE | 0 |
| 5 | 190 | UNKNOWN | — |

The changed 191-edge path is equivalent to published bank example 130. Explicit coordinate permutations, translations and orientation choices are checked and saved in `verification.json`. The two changed 190-edge paths are inequivalent to the two endpoint truncations of each of the 131 bank snakes under those symmetries. This finite comparison does not establish wider novelty.

More significantly, the most changed 190-edge path is exactly `[12] + p[2:]`, where p is the changed 191-edge path and begins `[7,15,13,...]`. Thus it retains a 190-vertex tail of a known example. Its change is confined to one end.

The six follow-up growth runs returned two 190-edge paths and four 191-edge paths. All four 191-edge paths are equivalent to bank example 130. The successful length recovery discarded vertex 12.

## Retaining the changed vertex

`protected.py` repeats repairs from the changed 190-edge seed while requiring vertex 12 to stay selected. This is a selected-vertex constraint, not an endpoint constraint. It tests faces 0, 3, 4 and 5 at exact lengths 191 and 192. All eight runs returned UNKNOWN after 20 seconds, without a feasible result. The script saves every status in `data/protected.json`. These timeouts exclude neither length.

## Verification

- The diversity objective and fixed-length model passed 608 independent exhaustive subset-oracle comparisons in dimensions 2 through 4, including infeasible restricted cases.
- The added selected-vertex constraint passed 256 independent exhaustive comparisons in Q3.
- All thirteen feasible paths in the first two phases pass independent unordered-pair checks. Outside membership and exchange counts are also checked.
- Three Lean results pass: equal selected sets give equal path order up to reversal; equal-size exchanges add and remove equally many vertices; a one-vertex deficit removes one more vertex than it adds.
- The prerequisite contiguity module was rebuilt and its five axiom audits passed.
- The full optimization model and the bank-comparison program remain finite computational checks, without an end-to-end Lean proof.

The proof runner writes each rebuilt prerequisite into a fresh build directory because Windows rejected replacement of an existing compiled module. Those local build products are excluded from version control.

## Reproduction

Run from the repository root with the project dependencies:

```text
python milestones/25-alternative-fillings/scripts/search.py
python milestones/25-alternative-fillings/scripts/protected.py
python milestones/25-alternative-fillings/scripts/protected_controls.py
powershell -File milestones/25-alternative-fillings/scripts/check_lean.ps1
python milestones/25-alternative-fillings/scripts/verify.py
```

These commands overwrite their named records; preserve prior runs first. The search models are heuristic experiments, and every INFEASIBLE or UNKNOWN statement is restricted to its encoded region and target.

## Collaborator refresh and next step

The branch `research/unconditional-241` advanced to 5fb6c286 with a clause-collector heartbeat adjustment. The other active branch advanced to e2d9f7fc with a seven-centre certificate generator. No further completed bound is adopted here. The previously reported 237 audit remains on the collaborator branch; this checkout integrates 238.

The next construction test should require an interior change in addition to the changed vertex, then compare resulting paths with the published bank before attempting growth. Endpoint-only substitutions and recovery of known classes must not be counted as new construction progress.
