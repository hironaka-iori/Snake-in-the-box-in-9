# Coarse singleton-count correction

Research checkpoint: 23 October 2026. This continues the requested empty-square route. The new results recover information hidden by the count symbol `6+` and combine it with empty-square shares. The exact optimum and the integrated global interval 191 <= a(9) <= 238 are unchanged.

## Checked geometric results

All coordinates below are normalized by renaming. H denotes an independently chosen integer from 6 through 21.

| Case | Eight directions | Seven internal singleton counts | Result |
|---|---|---|---|
| 0 | 01230143 | 3,3,H,3,3,H,3 | Excluded in Lean |
| 1 | 01230423 | 3,H,3,3,H,3,3 | Excluded in Lean |
| 2 | 01234120 | 6,3,3,6,3,3,6 | Excluded in Lean |
| 3 | 01234125 | 6,3,3,6,3,3,6 | Excluded in Lean |

The two interval exclusions also exclude their exact-six specializations. Cases 2 and 3 imply that if the counts are `(a,3,3,b,3,3,c)` with a,b,c >= 6, then a+b+c >= 19. Thus the seven-count sum is at least 31, and the three high positions carry at least one unit of excess beyond their coarse labels.

The four Boolean cores have 1,273, 1,223, 4,017 and 2,856 clauses, and 1,020, 987, 1,711 and 1,533 active variables respectively. They use **2,220,545 LRAT hints**. They have no share caps and no added cycle cuts. Native solver proofs were independently checked by drat-trim, then the extracted cores were re-solved for LRAT and replayed in Lean. Clause soundness and the geometric bridges were checked too.

**Nineteen final axiom audits passed**: eight refutation/geometric statements, eight arithmetic and overlap statements, and three statements converting exact exclusions into geometric excess. Only the applicable standard axioms `propext`, `Classical.choice`, and `Quot.sound` occur. See `data/verification.json` and `logs/`. This is an incremental build using milestone 28's existing support and geometry closure, not a fresh rebuild of every dependency.

## Three-position excess accounting

For a singleton count alpha_j, let b_j = min(6, alpha_j) and delta_j = alpha_j - b_j. Each qualifying case-2 or case-3 window starting at r has

```text
delta_r + delta_(r+3) + delta_(r+6) >= 1.
```

A position belongs to at most three such triples, because the possible starts are j, j-3 and j-6. For a set J of distinct qualifying starts, Lean checks

```text
|J| <= 3 * sum(delta_j).
G_12 >= 24 * sum(b_j) + 8 * |J| + sum(sigma_12(x)).
```

The second inequality uses the existing charge G_12 = 24*T + sum(sigma_12). It recovers eight integer charge units per qualifying window after paying for overlap. It does not prove a positive density of qualifying windows in every snake. The generic finite-set overlap theorem, the multiplicity-three bound, the exact coarse decomposition, and the charge consequence are in `lean/ExcessArithmetic.lean`; the snake-specific high-count inequalities are in `lean/ExcessGeometry.lean`.

## Diagnostic graph

The previous graph remembers seven directions, four count symbols, and a capped all-four suffix. Remembering a capped periodic 3,3,6 suffix adds 204 states, giving **44,336** total. Two interval-forbidden edges are deleted and two surviving edges receive the one-third-unit count correction. The recorded cycles are:

| Table | Before | After |
|---|---|---|
| Recorded share lower bounds | 119/29 | 119/29 |
| Recorded local-witness values | 859/180 | 287/60 |

The oracle remains pinned to `8ad204ffa32bb3bb114891ab089a50b83d0fc10e`. These are exact means of saved cycles, without a complete minimum-mean potential certificate or verified numerical share table. The graph experiment does not establish a new global bound. All saved cycle transitions are checked, and 393,216 reduced-alphabet count-history updates are checked independently of the graph search. These finite automaton checks are not Lean theorems about all sequence lengths.

## Stronger experimental targets

A separate CP-SAT model uses indicators for all 36 coordinate squares at each centre. It does not reuse the SAT counter or its 21-free-corner count reduction.

| Case | Solver exclusions for high-count sum | Positive local configuration | Experimental local minimum |
|---|---|---|---|
| 2 | at most 28 | counts 11,3,3,9,3,3,11 from milestone 29 | between 29 and 31 |
| 3 | at most 27 | counts 9,3,3,10,3,3,9 | 28 |

The case-2 cap-28 short run was UNKNOWN; a separate 45-second run returned INFEASIBLE. Both records are retained. These exclusions are **solver-only**, and are not used in the checked one-unit correction. No positive local configuration is asserted to extend to a complete snake.

Four fixed-selection controls check the experimental SAT sum counter against the known configurations, at the exact sum and one below. Repeated corner literals retain multiplicity: the 63 occurrences contain 55 or 57 distinct literals. The independent verifier checks the new positive configuration and all 225 cycle cuts saved in this milestone. A solver status alone is never treated as a Lean proof.

## Reproduction and provenance

Use Lean 4.19.0, pinned mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and the support paths recorded in milestone 28. The Windows paths in the scripts need adjustment on another machine.

```text
python -X utf8 scripts/archive.py --unpack
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/build.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check_excess.ps1
python -X utf8 scripts/verify.py
```

The archives are lossless and hashed. `scripts/certify.py` regenerates certificates, and `scripts/prepare.py` documents its adaptation from milestone 29. `scripts/independent.py` repeats the independent model and fixed-selection controls; `scripts/probe_excess.py` repeats the original SAT sum-cap tests. `scripts/correction_graph.py` repeats the graph experiment; `scripts/prepare_graph.py` records its derivation. Evidence file hashes and the dependency checkpoint are recorded separately.

The paper and the existing editor mirror contain the mathematical statements, with authors and hyperlink settings preserved. The built-in compilation attempt failed before TeX execution because of the Windows split-writable-root sandbox limitation. No current PDF or visual verification is claimed.

## Next proof obligation

The most direct strengthening is to certify the joint high-count sum, rather than enumerate every exact triple separately. The current geometric counter library proves bounds on each centre independently. A reusable soundness lemma for a counter whose literals concatenate the free corners at three centres would express the required joint bound. Multiplicities must be retained. Certificates for caps 27 and 28 would raise the proved window excess from one to ten and eleven respectively. The same three-position accounting would then apply. The unchanged lower-table cycle and the remaining numerical share certificates still need attention for a global result.

The 23 October GitHub refresh found no new commits beyond the previously inspected `d4936d72`, `86bd4daf`, and `e931afe8` collaborator checkpoints. Their proposed 235/230/231 proof chains have not been independently rebuilt here.
