# Round 216 linked-ledger and saved-chain review

Result: PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS. Independent audit of frozen research records, 15 November 2026. The audit ran only after the parent confirmed native session 72988 was terminal with exit 0 and the lock was absent. No compiler, solver, software tests, or new search was run.

## Version 2 transfer and predecessor link

The initial version 2 state reconstructs byte-for-byte from the round 215 final state with the documented changes: new engine pins, local jobs/nodes/time set to zero, empty local receipt list, history_parent, counter_scope=milestone-local, version 2 and the current transfer record. All five domain vectors, their order and identifiers, next_id 745, model pins, status and index are unchanged. Only the four pinned model files and the exact predecessor state snapshot are copied; prior run evidence remains at the linked predecessor.

The source state matches SHA-256 `1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb`. The source snapshot is byte-identical. The predecessor baseline is 740 jobs, 4,451,277 nodes and 422.129 reported solver seconds. The initial local-state hash is `48239c4300aaf613944e8239468217e10007d804f048de2abf3797f3f4111bc0`.

Verified the predecessor chain-audit hash and its exact final-state fields, together with every source pin recorded in that audit. Verified the linked publication-manifest hash and 754 selected manifest entries, including all 740 predecessor receipts plus the state, initial state, prior audit, engine files and model files. This checks the old receipt bytes without repeating their transition reconstruction or copying their directories. The declared publication reference is 670d633bca81e3efff8d8ba5db0a1ba7079af137; this bounded audit did not independently inspect that Git commit tree.

The transfer's three theorem receipts (TwoStep216, Joint216 and PathJoint216) match their pinned sources, objects, logs and dependencies and record successful acceptance. The source-review hash and all old/new engine and model pins match. No compiler was rerun. LiteralJoint216 is outside the transfer dependency set and outside this pin check.

## Local transition reconstruction

All 400 local accepted transitions, jobs 0 through 399, reconstruct exactly. The final local receipt list has no inherited entries, duplicates, missing records or extra uncommitted receipt. For each transition, the audit checked:

- Exact prior-state bytes/hash, selected last frontier entry, nonempty submitted domains and their containment in the original model root.
- Exact serialized input header and combined header/tail hash; frozen engine/model pins and stdout hash.
- ACCEPTED_TRANSITION, successful exit 0, no hard stop or stop reason, empty stderr, and stdout/receipt agreement for status, nodes, seconds and returned-region count.
- Containment of each returned region in the submitted region and pairwise disjointness, comprising 1,686 sibling comparisons.
- Exact removal of the selected last entry, consecutive allocation of fresh identifiers in native returned order, reverse append of those children, and preservation of the untouched frontier.
- Full frontier disjointness, including the initial state and all successors, comprising 14,665 comparisons; identifier uniqueness and allocation bounds.
- Exact local counters, immutable history_parent and counter_scope, receipt append, serialized successor bytes/hash, and the link to the next transition.

The runner's transition logic uses local counters and receipt paths consistently. The unchanged cumulative baseline remains in history_parent throughout the reconstructed chain. Summary jobs/nodes/seconds were checked as baseline plus local totals; new_jobs/local_nodes/local_seconds and joint-search-progress.case_states were checked against the local state. This avoids mixing cumulative and local counters.

## Recorded results

| Quantity | This milestone only |
|---|---:|
| Committed jobs |400|
| Exhausted subregions |353|
| Limited runs |47|
| Found witnesses |0|
| Visited nodes |2,044,830|
| Reported solver seconds |236.214|
| Returned unfinished regions |404|
| Recorded removal operations |208,637,851|
| Lexicographic removals |5|
| Simpler support calls |3,550,441|
| Simpler support removals |401,479|
| Simpler support failures |2,169|
| Saturated-budget encounters |121,404|
| Partner-matching calls |2,366,546|
| Partner-subset failures |3,753|
| Partner tight-set encounters |179,322|
| Partner tight-set removals |196,040|
| Word-matching calls |5,691,071|
| Word-subset failures |588,989|
| Word tight-set encounters |57,209,520|
| Word-subset removals |21,188,035|
| Joint pair removals |3,706,395|
| Joint triples examined |82,840|
| Joint sweeps |1,090|
| Joint new relations |0|

These are accumulated native operations, which can repeat across jobs. They do not count distinct globally excluded assignments or establish a controlled performance improvement.

All 400 jobs used a 3.0-second and 100,000,000-node budget. Minimum recorded startup free memory was 1,076,764,672 bytes; minimum sampled free memory was 900,112,384 bytes; maximum recorded native private memory was 9,928,704 bytes. Every startup gate recorded no other Lean process or query error. No accepted job recorded a resource stop. These are saved observations rather than an independent process-history trace.

## Final state

The batch stopped at its job budget. Its local final state remains OPEN with 400 jobs, 2,044,830 nodes and nine pending regions. Five transferred regions minus 400 submitted regions plus 404 returned regions leave 9 regions. Their stored identifiers are 20, 1138, 1137, 1136, 1135, 1148, 1147, 1146, 1145; next_id is 1149.

The cumulative totals are 1,140 jobs, 6,496,107 nodes and 658.343 reported solver seconds. The local final state and all receipt totals agree exactly with search-summary.json and joint-search-progress.json. Floating-point addition was reproduced in the runner's order; decimal seconds above are rounded for reading.

Final state SHA-256: `4599f3f699d81ee7e14295d537715d621db8a9bb5584ea8a9121d4f2ed592480`.

Both the local state bytes and the predecessor state hash were checked again after reconstruction and remained unchanged.

## Limits

This audit establishes the integrity of the linked baseline, copied inputs, local records and state accounting. Contained, disjoint returned regions do not independently prove that the native code omitted no satisfying assignment during propagation or retained every unfinished branch. Those claims still require the reviewed implementation and its model premises, or a separate traversal certificate. Generic geometry/path/Lean deductions remain distinct from full native traversal verification. Nine unfinished regions remain, so no exclusion of this complete model follows.

## Frozen evidence pins

- `scripts/audit_saved_chain.py`: `2f350912ee2c5e65f79f21328c9a520de8e4bc5a66ad0bc4b128b168b1520afd`
- `scripts/joint_continue.py`: `0f464816a4f862a6482966cab8f70f12e7b2b4afdabcd882d9f0bc0aeadacb36`
- `scripts/transfer_frontier.py`: `2a68afc90806fa9edb6e3ea6a8525f796b5052a83086616788d477659aa5696a`
- `scripts/joint_solver.c`: `6d025faf3620933ceaab7fd12c5d180f1c1bd6142e67de53950012fb162b1e91`
- `scripts/summarize_search.py`: `48ec1b43b1b8aa2126c24bb934f7aa82c66b290571ad14d9245d1692a742b23e`
- `data/frontier-transfer.json`: `ceaee59af690b43a7b1fa37cd6ebea4cbea67e5d53ff8aa09f417bffd645bd48`
- `data/search-summary.json`: `053501d96ddb0ab4d6f3276cb16845d7d859ae02fe9257dec10a758003297ed9`
- `data/joint-search-progress.json`: `ed8dca27ac48ff774ba272b3676e1ceede4efdbb8a92ecbe7b8c1ffac2cf9309`
- `data/TwoStep216-audit.json`: `a460a1b23d87a36ea750d76fd6060373c256458375f977a63f63ab6c21e5b674`
- `data/Joint216-audit.json`: `dde77bd661fa4fe883c3ea200c831d8bf312ed75b0463da59db11909ad136cd1`
- `data/PathJoint216-audit.json`: `c95330144c470376d75e1c4d37865cf4f980db1430933ed4d53cbeb3c2afa594`
- `logs/joint-engine-review.md`: `311aebef926bdf204e48e49fa2926e501ecff07acb0bd2c24f2859732e6595f2`
- `data/chain-audit.json`: `514d1aa5ec2759c410d878b850c276f7fd88c922457071e151f3a346aedd7559`
