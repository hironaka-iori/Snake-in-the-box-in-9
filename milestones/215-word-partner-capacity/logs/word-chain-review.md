# Round 215 saved transfer and transition-chain review

Result: PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS. Independent reconstruction of frozen research records on 15 November 2026. The audit was executed only after the parent confirmed native session 64294 had terminated successfully and the search lock was absent. No solver, compiler, software tests, or new search was run. Only the bounded record-audit script was executed.

## Transfer preservation

Verified all 1,448 source files against both the frozen round 214 directory and the copied round 215 evidence. The two overwritten state files are preserved byte-for-byte under the exact manifest aliases transfer214-state.json and transfer214-initial-state.json. The older source-state.json and source-initial-state.json snapshots remain unchanged. All 240 inherited receipts and associated files remain byte-identical.

Reconstructed the transferred initial state exactly from the round 214 final state by replacing engine_pins and retaining the explicit transfer_record path. All 13 frontier vectors, their order and identifiers, next_id, cumulative nodes/time, receipt order, model pins, status, index and version match. Old and new engine pins and model pins were checked against current bytes. The transfer's source-review and proof-receipt hashes match. The preserved PathWordCapacity215 receipt's source, object, log and dependency hashes also match; that is a pin check without rerunning Lean.

Source state SHA-256: `eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027`.

Transferred initial-state SHA-256: `3855cf64d3248724f6cbe113fb8bcc9043f2791ad0891faf6e57fc1183868ec2`.

## All 500 new transitions

The final state's receipt suffix contains exactly 500 new committed transitions, jobs 240 through 739, with no extra uncommitted or missing run receipt. For every transition, the audit independently verified:

- Exact previous-state bytes/hash and the selected final frontier entry; submitted domains have the correct length, are nonempty and lie inside the original model domains.
- Exact serialized input header, unchanged input tail and combined input hash; receipt engine/model pins and stdout hash.
- ACCEPTED_TRANSITION, exit 0, no hard stop or stop reason, empty stderr, and agreement of solver status, returned-region count, nodes and time with stdout.
- Returned-region containment in the submitted region and pairwise disjointness. There were 1,793 sibling-pair comparisons.
- Exact replacement semantics: remove only the selected final entry, assign fresh consecutive identifiers in native returned order, append those children in reverse order, and preserve every untouched frontier entry.
- All frontier pairs remain disjoint; the initial and 500 successor frontiers required 17,425 comparisons. Identifier uniqueness and allocation bounds were also checked.
- Exact cumulative counters, appended receipt path, serialized successor bytes/hash, and linkage to the next saved state.

The runner diff against round 214 changes only source/executable names and batch-output names. The one_job state-update and acceptance logic is unchanged.

All 500 headers used 3.0 seconds and 100,000,000 nodes per job. Startup gates recorded no other Lean process or query error and at least 1 GiB free memory. Minimum recorded gate free memory was 1,590,611,968 bytes; minimum sampled free memory was 1,571,729,408 bytes; maximum recorded native private memory was 9,940,992 bytes. No resource-stop or interrupted transition occurred. These are saved observations, without an independent historical process trace.

## New-work totals

| Quantity | New 500 transitions |
|---|---:|
| Exhausted subregions |437|
| Limited runs |63|
| Found witnesses |0|
| Visited nodes |2,650,260|
| Reported solver seconds |296.922|
| Returned unfinished regions |492|
| Recorded removal operations |262,752,199|
| Lexicographic removals |3|
| Simpler support calls |4,834,232|
| Simpler support removals |425,382|
| Simpler support failures |2,682|
| Saturated-budget encounters |143,690|
| Partner-matching calls |3,143,942|
| Partner-subset failures |3,910|
| Partner tight-set encounters |219,053|
| Partner tight-set removals |239,872|
| Word-matching calls |7,665,801|
| Word-subset failures |841,841|
| Word tight-set encounters |76,199,990|
| Word-subset removals |29,311,693|

Counters record native operations, including repeated encounters and removals. They do not measure distinct globally excluded assignments. This batch does not provide a controlled performance comparison with earlier engines.

## Final reconstruction and summary agreement

The final state bytes match the independent reconstruction exactly. Both search-summary.json and word-search-progress.json agree with all reconstructed counts, the 500 receipt hashes and the final state. The batch stopped at its job budget. The frontier accounting is 13 inherited regions minus 500 submitted regions plus 492 returned regions, leaving 5 regions.

The final state is OPEN, with 740 total committed jobs, 4,451,277 cumulative nodes, 422.129 cumulative reported solver seconds, and next_id 745. Final frontier identifiers, in stored order, are 20, 712, 711, 710, 738.

Final state SHA-256: `1e53d7824e4350092104072ba5c1506236f8af19969f09346ab3c3f517e7eacb`.

Floating-point accumulation was reproduced in the runner's order; rounded seconds above are for reading only. The final state was checked again at the end of the audit and had not changed.

## Limits

The audit establishes preserved inputs, consistent linked records, domain containment/disjointness and exact state accounting. It does not independently establish that the native implementation omitted no satisfying assignment during propagation or returned every unfinished search branch. Those claims depend on the separately reviewed C implementation and saved-model premises. Generic Lean counting results, the actual-path bridge, and native traversal certification remain separate. Five pending regions remain, so this model has not been excluded. The inherited 240 transitions were preserved and hash-checked without repeating their earlier reconstruction or executing their searches.

## Frozen evidence pins

- `scripts/audit_saved_chain.py`: `b84b04925d9a8df71bbe617ebacc902d08675eab855c083c064de0e7beac3be3`
- `scripts/word_continue.py`: `44cf914f35468428fea3b9cd938182a23a7743bb247acd91ae81ca7bf0f14276`
- `scripts/transfer_frontier.py`: `b2a240aa631ac7e6713fb37089c6e4468cd63c5270104b58e633f4eeec1d3fc8`
- `scripts/word_solver.c`: `b9dc79b25ff57219066babfe3f10355823ad10605aa199318826e0cbf558df1e`
- `data/frontier-transfer.json`: `07562a7cb079451ffb00b2f16a6ceb0d5f8f2fd9fdb8cef22e615f2f40a69dc6`
- `data/search-summary.json`: `cebd027fd26de645d0a22f932bb66ec3a21469755c6bcd6339b14432c457fe64`
- `data/word-search-progress.json`: `3cbc6806716fafc473489af03945feacc582635c0d4ebd5c6df74534eb662507`
- `data/PathWordCapacity215-audit.json`: `4dde9c31377a9fe9cc3d7d3115ad4d7dfded150bc6235d7cb04667b213966b21`
- `logs/word-engine-review.md`: `459ad460475ea6c59519b9c68df63d0a11ff019c80a04a1e58358e5f7dc943ac`
- `data/chain-audit.json`: `95826711a80c30cae0113e9862e14837cd2f7a555f269a1272b09bfb9f71f621`
