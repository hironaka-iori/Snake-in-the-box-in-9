# Audit of the open case 24 and case 9 chains

The frozen authoritative receipt chains are internally consistent. Both cases remain `OPEN` with pending work; neither audited state supports an exhaustion conclusion. This was a read-only audit of saved calculation evidence. No native search, compiler, or software tests were run.

## Exact recorded totals

| Item | Case 24 | Case 9 |
|---|---:|---:|
| Fixed coordinates | $[0,4]$ | $[3,4]$ |
| Status | `OPEN` | `OPEN` |
| Committed jobs | 100 | 100 |
| Authoritative linked receipts | 100 | 100 |
| Pending jobs | 5 | 6 |
| Next unused job identifier | 105 | 106 |
| Reported search nodes | 3,430,077 | 3,177,434 |
| Sum of reported solver time | 108.975 seconds | 99.188 seconds |
| Native `LIMIT` transitions | 12 | 11 |
| Native `EXHAUSTED` transitions | 88 | 89 |
| Largest committed frontier | 13 | 13 |
| Orphan receipt files | 0 | 0 |

The last case 24 transition exhausts job 102 and leaves five pending jobs. The last case 9 transition exhausts job 100 and leaves six pending jobs. These are exhausted subproblems within open cases.

## Verified chain consistency

For each case, the initial state contains exactly the original model-domain job with zero counters and an empty receipt list. Initial and current engine/model pins agree. All six current engine-file hashes and all three model-file hashes match their stored pins. The common input tail matches a reconstruction from the saved constraint rows, forbidden tuples, and permutation list.

All 200 authoritative linked transitions were inspected. Each saved before-state equals the previous authoritative after-state byte for byte. Each receipt's before/after hashes, input-head-plus-common-tail hash, and native-output hash match the corresponding saved files. Input dimensions, budgets, and initial domains identify exactly the last pending job selected from that before-state.

Every receipt records acceptance, exit code zero, and no hard termination. Native status, returned-frontier count, node count, and time agree with its receipt. All returned pending vectors have the correct dimensions, nonempty masks contained in the selected job, and pairwise disjoint product domains.

For every transition, the entire after-state equals an independently reconstructed update: remove only the selected last job, insert all returned vectors with the recorded fresh identifiers and order, preserve the other pending jobs, update counters, and append exactly that receipt. The final current state equals the last authoritative after-state. Reported cumulative nodes and times equal the sums of linked native outputs. No duplicate receipt path or duplicate pending-job identifier was detected.

No orphan receipts were present in either case directory. Every linked receipt has a null `stop_reason`. The existing interpretation of `STOP` as an internal per-job marker is unchanged; manual batch cancellation is not promised.

## State anchors

Case 24 current state SHA-256:

`833ca39676a024c245971b7d9d714a4990164121a78f9e09d5144a9b6c78fcfa`

Case 9 current state SHA-256:

`4d57547675175d726ed112c23cb3bc7c623f1e0735132b635796db382b5ee3f6`

## Scope

The audit found no broken evidence link or incorrect state replacement. It does not independently prove that native propagation and traversal cover every admissible assignment, and it supplies no Lean certificate for either chain. The nonempty frontiers retain unresolved regions. Counts of exhausted individual jobs do not establish that either complete coordinate-history model is exhausted.
