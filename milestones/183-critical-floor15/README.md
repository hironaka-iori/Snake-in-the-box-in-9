# Round 183: the critical floor-15 certificate

This is the first of two requested rounds, 183 and 184. Continue through round 184 and then pause. The maintained project range is 191–235, with the archived upper-bound proof's independent rebuild pending. No new unconditional bound or construction is claimed.

The radius-four 012034 query excluding integer five-centre share at most 14 returned UNSAT in about 31.97 seconds. It uses broad internal-count intervals [0,21] and the saved local degree, endpoint-budget, square and six-cycle constraints. No new path-extension or additional cycle clauses were added for this shape. The streamed cap transformation is the one from round 182; its truncation arithmetic already has an accepted Lean proof. Complete interpretation of the Boolean input as an arbitrary snake remains unfinished.

The full proof passed native ordered-RUP replay: 119,146 added clauses and 4,922,578 propagation hints, including the final empty clause. A dependency-closure extraction then retained 12,424 original clauses and 52,489 deductions with 3,619,677 hints. The extracted proof was independently replayed from its new core input. Dense variable renaming reduced the variable range to 5,342, and this renamed proof also passed full native replay.

| Certificate | Original clauses | Derived clauses | Propagation hints | Declared variables |
| --- | ---: | ---: | ---: | ---: |
| Full streamed input | See `data/012034-floor15.json` | 119,146 | 4,922,578 | See solver record |
| Dependency core | 12,424 | 52,489 | 3,619,677 | Original variable range |
| Dense core | 12,424 | 52,489 | 3,619,677 | 5,342 |

The core extraction follows every positive propagation hint backward from the final empty clause. It retains all referenced original clauses, keeps the needed derived clauses in their original order and changes clause identifiers consistently. Dense renaming applies one injective variable map to both the input and every derived clause. The new proof replays verify the resulting inputs directly; no deletion or unchecked derived clause is required to justify the contradiction.

A last-use schedule needs at most 12,593 simultaneously stored clauses, counting the new clause before releasing its last-used premises. This is below the existing checker's 14-bit slot limit, and 5,342 variables fit its offset 8192. This is an exact storage measurement and a format-feasibility result. No full Lean replay has been run, and no runtime or memory success for the future kernel replay is promised. The deletions were measured rather than emitted into the saved dense proof.

The core still uses all main base clause families, including the endpoint counter and cycle exclusions. It does not justify dropping those geometric assumptions. The full Boolean semantics and initial-database truth bridge must accompany any eventual Lean contradiction certificate. The older share-18 replay remains separate at 33,111/145,215 deductions; these new proofs do not extend that older checkpoint.

## Consequence for the next round

The existing floor-14 profile has a critical nine-edge cycle of weight 4448. Six edges have shape 012034, whereas none has shape 012301. Round 182 established that raising only 012301 to 15 cannot remove the loss-zero and loss-one obstruction in the current comparison. The new 012034 certificate supplies the local evidence relevant to that critical cycle.

Round 184 should first examine profile (15,14,14,14), ordered as 012034, 012301, 012340 and 012345. If necessary, compare (15,15,14,14), using the round-182 representative-extension certificate. Reconstruct the weights from original source rows, preserve the retained graph's exact unresolved premises, scan every edge of an accepted potential, and check the resulting actual-snake conditional arithmetic in Lean. Do not infer a global result from the local native certificates alone.

## Saved evidence

- `data/*-replay.json`: completed native replay receipts for the full, core and dense proofs.
- `certificates/`: compressed inputs, proofs, cap meanings, original clause mappings and variable mappings.
- `data/012034-floor15-dense.json`: the exact variable and last-use storage measurements.
- `data/core-tags.json`: clause-family counts; this is an audit of what remains necessary in the extracted proof.
- `scripts/`: exact producer, dependency extraction, variable-renaming and replay sources.
- `cache/`: uncompressed files retained locally and excluded from publication.
- `source-before/`: manuscript and short explanation before the update.

The solver retained its 90-second and 128 MiB raw-proof limits. Replay and trimming retained the 1 GiB startup threshold, 256 MiB private-memory cap, 768 MiB free reserve and 240-second bound. No resource guard was weakened. Native verification remains distinct from Lean verification and from geometric interpretation.
