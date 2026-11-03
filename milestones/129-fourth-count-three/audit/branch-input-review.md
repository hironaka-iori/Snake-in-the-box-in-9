# Independent input and complete native proof review

The audit passes. The four new counters match their intended counts, signs, multiplicities and variable allocation. Their 3014 clauses were reconstructed independently, and the retained 104529-clause input is unchanged. A complete streaming replay of the native proof then derives the empty clause from the resulting 107543-clause input.

This is a checked propositional contradiction for the branch with fourth count equal to three and six-count total at most 22. The complete actual-snake interpretation and Lean certificate replay remain separate obligations. The branch with fourth count at least four, a six-count floor for the entire direction class, and any global length bound are not established by this audit.

The auditor imports no preparation or encoding helper. It independently enumerates cube corners, constructs all new counters, verifies their threshold semantics, and processes the entire proof with deletions. No solver, compiler or other job was started, stopped or changed. Only the three assigned audit files were written.

## Branch and mathematical interpretation

The normalized directions are 0120324, with vertices

\[
(0,1,3,7,6,14,10,26).
\]

The six counts are the singleton-square counts at internal positions one through six. The retained input already requires the fourth count to be at least three. The new upper bound of three therefore restricts it to exactly three.

For an actual snake in this branch, the checked first/fourth exclusion forces the first count to be at least three. The checked second/fourth pair bound gives a second count of at least five. Together with the six-count total at most 22, these imply

\[
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}
\le22-3-5-3=11.
\]

These are the intended meanings of the four added constraints. The existing theorem sources and receipt pins were checked against the preparation provenance. This source provenance does not replace the concrete semantic proof for the complete new input.

## Input reconstruction

The first 104529 clauses agree exactly with the milestone-128 input, including literal order. The old body bytes form an exact prefix of the new body; the header necessarily changes to record the new variables and clauses. An independent serialization of the whole reconstructed input agrees byte for byte with `work/three.cnf`.

All six corner lists were recomputed from the cube. For each internal centre, one enumeration flips each allowed pair of coordinate directions, and another tests all 512 vertices for the required Hamming distance and excluded directions. Each list has 21 distinct corners, and its order agrees with the saved data.

Selected-vertex variable \(X_v\) has identifier \(v+1\). Positive literals count selected corners; negative literals count absent corners. Consequently the two positive counters below express lower bounds on absence, while the two negative counters express upper bounds on absence.

| Counter | Literal meaning | Occurrences | Cap | New clauses | New variables | Variable identifiers |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| First count at least 3 | Selected corners at position 1 | 21 | 18 | 758 | 378 | 8706–9083 |
| Second count at least 5 | Selected corners at position 2 | 21 | 16 | 676 | 336 | 9084–9419 |
| Fourth count at most 3 | Absent corners at position 4 | 21 | 3 | 143 | 63 | 9420–9482 |
| Sum of counts at positions 3, 5 and 6 at most 11 | Absent corner occurrences | 63 | 11 | 1437 | 693 | 9483–10175 |
| Total | | | | 3014 | 1470 | 8706–10175 |

The fourth-count lower bound is retained explicitly: the base contains all 210 direct clauses requiring at least three absent corners at that centre. Their completeness and occurrence in the base were checked independently again. Together with the new at-most-three counter, they express equality of that count to three.

The first three new lists each contain 21 distinct vertices. The final list has 63 occurrences from 57 vertices. Vertices 13, 31, 47, 79, 143 and 271 each occur twice, and the other 51 occur once. Every repeated negative literal is preserved. The final list is sorted by its signed literal, exactly as saved; it is not deduplicated.

The four counter indices are exactly 9, 10, 11 and 12. Every saved clause, tag and register meaning agrees with the independent construction. All 1470 fresh registers have identifiers above 8705, are disjoint between counters, and are disjoint from the retained input. The new clauses use only selected-vertex variables and their own new registers. The complete input declares 10175 variables, of which 7718 occur; the previously removed 2457 register variables remain unused.

## Counter semantics

For a counter on \(n\) literal occurrences with cap \(k\), register \((i,j)\) means that at least \(j+1\) of occurrences zero through \(i\) are true. An occurrence is true when its corner is selected for a positive literal and absent for a negative literal. Equal vertex literals at different positions remain separate occurrences.

If at most \(k\) occurrences are true, assigning every register its threshold value satisfies the initialization, monotonicity, step and overflow clauses. The independent audit checks every emitted clause for every feasible local combination of previous prefix count and next occurrence value, including the two negative-literal counters. Across the four counters, 2356 local assignments produce 62588 successful clause evaluations.

Conversely, the clauses force each threshold that is attained by the actual occurrence count. Induction over the occurrence positions uses the first-threshold clause when a true occurrence begins the count, monotonicity for thresholds already attained, and the step clause when another true occurrence reaches a higher threshold. A \((k+1)\)-st true occurrence would then contradict its overflow clause. Thus each counter expresses exactly its stated cardinality constraint after existentially quantifying its registers.

The numerical clause totals agree with \(k+(n-1)(2k+1)\), and the register totals with \(nk\). This review provides the ordinary mathematical counter argument and checks every concrete clause. It does not claim a new Lean semantic theorem.

## Complete native proof replay

The native process returned exit code 20 with an UNSAT result in 50.078 seconds. Its recorded CPU use was 6.0625 seconds. The saved raw proof has 46668010 bytes. Its hash, the input hash, the terminal record, the output logs, the solver executable and the search source all match their recorded pins.

Before replay, the auditor required at least 1 GiB of available physical memory. The observation was 6709821440 bytes. The proof was processed as a stream; its complete text was never loaded into memory. The clause database retained only currently available inputs and deductions.

For every deduction, the auditor checked that its identifier was fresh and larger than every earlier deduction identifier, its literals used valid variables, and every positive reference named a currently available earlier clause. It assumed the negation of the proposed clause and replayed each reference in order. A referenced clause had to be unit or contradictory under the current assignment. The final reference had to yield a contradiction, with no references following that conflict. Satisfied or non-unit references were rejected. Every deletion target had to be available before removal.

| Replay measurement | Result |
| --- | ---: |
| Input clauses | 107543 |
| Checked deductions | 90825 |
| Ordered positive references | 5779098 |
| Deletion records | 17870 |
| Deleted clause identifiers | 119216 |
| Maximum live clauses | 107544 |
| Live clauses after replay | 79152 |
| Maximum references in one deduction | 806 |
| Physical proof lines processed | 108695 |
| Final derived identifier | 198368 |
| Final derived clause | Empty |

The live-clause total also agrees with \(107543+90825-119216=79152\). The streamed hash equals the full raw-file hash, so the replay covers the entire saved trace rather than a prefix. Replay completed in 5.062 seconds. The final derived clause is empty and has a complete checked ordered derivation.

The terminal search record retains its original `NATIVE_UNSAT_COMPLETE_REPLAY_PENDING` status. The separate audit evidence records `PASS_COMPLETE_POSITIVE_RUP_BRANCH_REFUTATION`; no earlier record was rewritten to reflect the later check.

## Scope and remaining obligations

The new counters are inputs to this replay. The audit does not establish that they are RUP consequences of the older unrestricted formula. In particular, imposing fourth count at most three selects a branch and cannot justify discarding the fourth-count-at-least-four branch.

The result establishes unsatisfiability of the exact restricted propositional input. To turn it into the intended checked statement about actual snakes, the proof workflow must supply the concrete interpretation of the retained clauses and all four new counters, preserve the occurrence multiplicities, complete the exported contradiction checks in Lean, and compose them with the actual-window normalization and branch conditions. Independent theorem checks for parts of that interpretation are separate evidence.

If those obligations are completed, the resulting conclusion concerns the impossibility of fourth count three under this pattern and total cap. It would sharpen a necessary condition within the unresolved count problem. It would not itself prove a six-count floor of 23, eliminate the fourth-count-at-least-four branch, or improve the global snake-length bound.

## Saved evidence

The auditor runs read-only unless an output path is supplied. Its `--terminal` option checks the saved terminal result and selects the appropriate verification: complete streaming replay for UNSAT, independent full-assignment and selected-graph validation for SAT, or an optional 1000-deduction prefix after a timeout. Only the complete UNSAT replay was used for this saved review. An output file is created exclusively and cannot overwrite existing evidence.

The JSON preserves all counter occurrence lists, repeated vertices, signs, caps, allocation intervals, clause-family counts, local semantic-check totals, complete replay statistics and source pins. Every pinned input was rehashed after the audit to detect concurrent changes.

| Artifact | SHA256 |
| --- | --- |
| Independent auditor `audit/audit_branch.py` | `9a8c407e90872325877342320ac8dfcd8fd0de9412bc9f853ba013c10e691a5c` |
| Saved evidence `data/branch-review.json` | `cc36e59e08ec3d2851c57b0279a0a16f9f3bf288b4082623c702cc7224ca6819` |
| Complete branch input `work/three.cnf` | `0d5e7e62e3c7ea54ffdabc02cf1d9d27c651fe3fd179320cc83f014ff9ac1ccd` |
| Counter detail `data/branch-counters.json` | `61dfa77e2bcee6a356e5e807e11eb0d786d2703f7757bc2e3743332d168f233b` |
| Preparation record `data/preparation.json` | `5ec844920cd6ebd1b26807ce358f0ee812dd910681ffa93a01646a56f4e4dcfc` |
| Terminal search record `data/search.json` | `b37f463053dbdcf8d4d89c1b9777c33dc4b619610aa902d52fa1b40ce42a344c` |
| Complete raw proof `work/three.raw.lrat` | `f0ecb0411fd46f7c0f7bd85fbe9ed56062b7f1c99f35354532f4fb3d94213801` |
| Retained milestone-128 input | `a00f07497e7e1f4bf3e9bd31d74c1ef39999ebdc0d1019aecc860493ac05d2fc` |

The audit completed at 2026-11-03 07:04:11 UTC. No substantive defect was found in the restricted input or the complete native refutation within the scope above.
