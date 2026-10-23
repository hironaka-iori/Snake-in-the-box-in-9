# Joint singleton-count bounds

Research checkpoint: 23 October 2026. This milestone strengthens the one-unit excess result from milestone 30. The general snake optimum remains unresolved, and the integrated global interval remains 191 <= a(9) <= 238.

## Geometric results

For seven consecutive internal centres with singleton counts $(a,3,3,b,3,3,c)$, where $6\le a,b,c\le21$, the following statements passed Lean, including the interpretation for an arbitrary snake under coordinate renaming:

| Directions | High-count sum | Excess beyond three coarse sixes |
|---|---|---|
| 01234120 | $a+b+c\ge29$ | $(a-6)+(b-6)+(c-6)\ge11$ |
| 01234125 | $a+b+c\ge28$ | $(a-6)+(b-6)+(c-6)\ge10$ |

The final gate is `data/verification.json`. **All 20 axiom audits passed**, using only the applicable standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

The generic counter argument is in `lean/JointCountTags.lean`. It checks counter clauses assuming primitive input literals and an actual bound on their true occurrences. `valid_append` combines previously checked per-centre counters with an additional joint counter. `three_centre_count` proves that the concatenation of three opposite-corner lists gives the sum of their singleton counts. Shared vertices retain their multiplicities; removing duplicates would change the counted quantity.

`lean/JointCountBridge.lean` exposes exact preservation of each centre's count under translation and coordinate permutation. The generated `SumWindow2.lean` and `SumWindow3.lean` use that equality to transfer the joint-sum refutations to arbitrary snakes. The direction normalization hypothesis is explicit through a coordinate permutation; no normalization existence is assumed as an axiom.

## Certificates

| Case | Refuted sum cap | Core clauses | Active variables | LRAT hints |
|---|---|---|---|---|
| 2 | 28 | 4,376 | 1,758 | 2,919,901 |
| 3 | 27 | 4,080 | 1,789 | 1,904,503 |

The total is **4,824,404 LRAT hints**. Native proofs were checked by drat-trim, and separate LRAT proofs of the extracted cores were replayed in Lean. Each starting model includes 93 saved cycle cuts; every one is checked independently as an induced cycle, and each retained clause also passes its Lean geometric tag check. The proofs do not use an empty-share cap.

The 20 audits cover ten generic counter statements, exact geometric count preservation, three weighted-excess statements, two generated clause-soundness theorems, and four refutation/geometric consequences. These checks reused milestone 28's compiled support and geometry dependencies. This is not a fresh rebuild of the entire proof closure.

## Improved charge accounting

Let $b_j=\min\{6,\alpha_j\}$ and $\delta_j=\alpha_j-b_j$. Let $J_2,J_3$ be disjoint sets of qualifying starting positions for the two patterns. The multiplicity-three argument from milestone 30 and the weighted overlap theorem give

$$
11|J_2|+10|J_3|\le3\sum_j\delta_j.
$$

Consequently,

$$
G_{12}\ge24\sum_jb_j+88|J_2|+80|J_3|+\sum_x\sigma_{12}(x).
$$

Thus the count correction contributes 88 or 80 integer charge units per qualifying window. The saved lower-table cycle of mean 119/29 and witness-table cycle of mean 287/60 both avoid these windows. Strengthening only these weights therefore leaves those particular cycles available; no new global upper bound follows.

## Positive configurations and remaining numerical gap

The independently checked case-3 local forest from milestone 30 has counts `(9,3,3,10,3,3,9)`, with high sum 28. A new case-2 local forest has counts `(11,3,3,9,3,3,10)`, with high sum 30; its vertex set is saved in `data/positive-2-30.json` and checked independently. No extension to a complete snake is claimed.

The further case-2 test at cap 29 returned UNSAT, suggesting a stronger lower bound of 30. That result remains solver-only. It is not used in the checked lower bound 29 or in the displayed charge correction.

The next witness-table cycle has all-four counts and two additional seven-centre direction shapes. Both were solver-excluded. This motivated the separate direction-independent investigation in [milestone 32](../32-seven-count-four-screen/README.md).

## Reproduction

Use Lean 4.19.0 and the pinned mathlib/support environment documented in milestone 28. The scripts contain local Windows paths which must be adjusted on another machine.

```text
python -X utf8 scripts/archive.py --unpack
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/build.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/check_weighted.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/replay.ps1 -Case 3
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/replay.ps1 -Case 2
python -X utf8 scripts/verify.py
```

The generator `scripts/certify.py` rebuilds both CNFs, cycle-cut checks, proof extractions, LRAT exports and clause-soundness sources. `scripts/prepare.py` records the adaptation of the three original counter-clause proofs; `scripts/wrappers.py` regenerates their snake interpretations. `scripts/positive.py` repeats the case-2 positive search. Archives and source hashes are recorded in `data/`.

The mathematical paper and its existing editor mirror have been updated. Author and hyperlink metadata are preserved. The built-in preview compiler failed before TeX execution with the Windows split-writable-root sandbox error, so no current PDF or layout verification is claimed.
