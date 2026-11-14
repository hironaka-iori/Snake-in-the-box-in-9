# Case 18 receipt and state-chain audit

A read-only audit of the saved mathematical calculation evidence found no inconsistency in the authoritative case 18 chain. The audit used the 51 receipt paths linked by `data/case-18/state.json`; it did not rerun the native search, compile software, or run software tests. Cases 24 and 9 were left untouched.

## Observed terminal record

| Item | Audited value |
|---|---:|
| Fixed coordinates | $[1,4]$ |
| Free block coordinates | Six |
| Residual permutations | 120 |
| Current case status | `EXHAUSTED` |
| Current pending jobs | 0 |
| Committed jobs and linked receipts | 51 |
| Native `LIMIT` returns | 6 |
| Native `EXHAUSTED` returns | 45 |
| Sum of reported search nodes | 1,713,998 |
| Sum of reported solver time | 41.908 seconds |
| Largest committed pending frontier | 10 jobs |
| Unlinked receipt files in this case | 0 |

The time is the sum of the native solver's recorded times, rather than a fresh wall-time measurement.

## Initial data and pins

The initial state is the expected open root problem: job zero contains exactly the model's root domains; `next_id` is one; the committed-job, node, and time counters are zero; and the receipt list is empty.

The six current engine-file hashes and three model-file hashes match the stored pins. Initial and current states carry identical pins. Every linked receipt and every corresponding before/after state carries those same pins.

The common input tail was independently reconstructed from the saved model's binary rows and forbidden tuples followed by the saved permutation list. Its bytes match `input-tail.txt` exactly. Thus the tail used by the receipt checks encodes those pinned data, rather than merely being a separately matching opaque file.

The initial state SHA-256 is:

`1b978a81774f9f56e967fba78a556963958a42a6445156279cec58f97e293684`

The current terminal state SHA-256 is:

`b0de23c26f2ec3e2745ac6b7afc3983d28ba9e70063c2f88e5cedfac160fa585`

## All 51 authoritative transitions

For every linked receipt, the audit verified:

1. The saved before-state bytes equal the preceding authoritative after-state bytes, starting from `initial-state.json`.
2. The receipt's before and after hashes match the corresponding saved state files.
3. The hash of the run's input head followed by the common tail matches the receipt's input hash.
4. The head declares the correct dimensions and constraint counts, a positive finite budget, and exactly the domains of the last pending job in the before-state.
5. The saved native output matches the receipt's standard-output hash, solver status, node count, time, and returned-frontier count.
6. The receipt records an accepted transition, exit code zero, and no hard termination.
7. Every pending vector has the required length, nonempty masks, and masks contained in the selected input job. Every pair of returned regions has disjoint masks in at least one coordinate.
8. The complete after-state equals an independently reconstructed update: remove exactly the last pending job; assign consecutive fresh identifiers to all returned vectors; insert those children in reverse order; retain all other pending jobs; increment the stated counters; and append exactly this receipt path.

All those comparisons passed. No authoritative receipt path is repeated, and every committed frontier has distinct job identifiers. Every linked receipt has a null `stop_reason`.

The six refining transitions are:

| Receipt ordinal | Selected job | Returned regions | Pending after commitment |
|---:|---:|---:|---:|
| 1 | 0 | 10 | 10 |
| 10 | 9 | 7 | 8 |
| 18 | 10 | 9 | 9 |
| 27 | 26 | 8 | 8 |
| 35 | 34 | 9 | 9 |
| 44 | 43 | 7 | 7 |

Each of the other 45 transitions records `EXHAUSTED` with an empty returned frontier and removes exactly its selected job. The last transition exhausts job 50 and reduces the pending frontier from one to zero. The current state bytes equal that last after-state exactly. Its cumulative node and time counters equal the sums of all 51 native outputs.

Enumeration of receipt files under case 18 found no orphan receipts. No unlinked result was used to justify a state transition.

## Meaning and limitations

The saved chain is internally consistent with terminal native exhaustion of this normalized six-coordinate model. It contains no missing receipt, broken hash link, omitted returned region, or unintended change of the selected pending job detected by this audit.

The audit checks recorded evidence and the exact state-update calculation. It does not independently prove that each native `EXHAUSTED` return refutes every acceptable assignment, or that each native `LIMIT` frontier covers every unrefuted assignment. Those claims retain the native traversal and geometric model obligations discussed in the implementation review. The generic Lean coverage lemmas do not certify this concrete chain, and matching an executable hash does not itself prove the executable implements the reviewed source.

`STOP` remains an internal per-job checkpoint marker. The existing implementation does not promise that a manually created per-run marker cancels the entire batch; that limitation is unchanged. No stop-triggered transition occurred in this authoritative chain.

The conclusion is specific to the saved source, fixed indexed coordinate histories $[1,4]$, unchanged length, normalization, forbidden assignments, and global lex constraints. It is neither a classification of all cube paths nor a new global snake-length bound.
