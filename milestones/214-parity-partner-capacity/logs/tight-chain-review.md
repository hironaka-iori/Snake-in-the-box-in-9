# Round 214 saved transfer and transition-chain review

Result: PASS_SAVED_TRANSFER_AND_120_TRANSITIONS. Independent reconstruction of frozen research records, 15 November 2026. No solver, compiler, software tests, or new search was run. The only execution was the bounded read-only record audit; it wrote its own receipt.

## Transfer

Verified the complete manifest of 726 source files against both the frozen round 212 directory and the copied round 214 evidence. The two intentionally replaced files are preserved byte-for-byte as source-state.json and source-initial-state.json. All 120 inherited receipts and their associated files remain unchanged.

The transferred initial state is reconstructed byte-for-byte from the round 212 final state by changing only engine_pins and adding transfer_record. All 11 unfinished region vectors, their order and identifiers, next_id, cumulative nodes/time, inherited receipt order, model pins, status, index and version are unchanged. Verified old and new engine pins, all model pins, and the transfer's source-review and proof-receipt hashes. The preserved TightPartner214 receipt, source, object, log and dependency hashes match; this was a receipt/pin check, without rerunning Lean.

Source state SHA-256: `6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8`.

Transferred initial state SHA-256: `c4c5631842a607a4c4a26d7621cd913f8a2122d35964246ec0fa0ece4e96c6ee`.

## New transitions

Inspected all 120 new accepted receipts, jobs 120 through 239, in the final state's exact order. No extra or missing run receipt was found. For every transition, independently checked:

- Exact previous-state bytes and hash, selected final frontier entry and identifier, nonempty domains contained in the model root.
- Exact serialized input header, immutable input-tail hash, combined input hash, source/executable/model pins and stdout hash.
- Successful exit 0, ACCEPTED_TRANSITION status, no hard stop or stop reason, empty stderr, and consistency of solver status, node/time counters and returned-region counts.
- Every returned region is nonempty coordinatewise and contained in the submitted region; all returned pairs are disjoint in at least one coordinate. This covered 449 sibling comparisons.
- Exact runner replacement: remove only the selected final entry, allocate fresh increasing identifiers in returned order, append the new entries in reversed order, and preserve all untouched frontier entries.
- Full frontier pairwise disjointness, including the transferred frontier and each reconstructed successor, covering 7085 comparisons. Fresh identifier uniqueness and upper bounds were checked.
- Exact cumulative counters and receipt append, serialized successor bytes and hash, and linkage to the next saved state.

All input headers used a 2.0-second and 100,000,000-node budget. All 120 resource gates recorded no other Lean process or query error and at least 1 GiB free memory. The minimum recorded gate free memory was 1,398,665,216 bytes; minimum sampled free memory was 1,389,318,144 bytes; maximum recorded native private memory was 9,916,416 bytes. No resource-stop transition occurred. These are recorded observations, without an independent process-history trace.

## New-work totals only

| Quantity | New 120 transitions |
|---|---:|
| Exhausted subregions |105|
| Limited runs |15|
| Found witnesses |0|
| Visited nodes |749,506|
| Reported solver seconds |49.130|
| Returned unfinished regions |122|
| Recorded removal operations |45,380,059|
| Lexicographic removals |0|
| Simpler support calls |643,282|
| Simpler support removals |50,063|
| Simpler support failures |251|
| Saturated-budget encounters |74,237|
| Partner-matching calls |642,914|
| Partner-subset failures |120|
| Tight-set encounters |167,416|
| Tight-set removal operations |3,054|

These are accumulated native operation counters. Repeated encounters and removals do not count distinct globally excluded assignments, and this batch is not a controlled timing comparison.

## Final state and summary agreement

The final serialized state was reconstructed exactly and matches both search-summary.json and tight-search-progress.json. The progress reason is BUDGET. The inherited 11 regions, minus 120 submitted regions, plus 122 returned regions leave 13 unfinished regions.

The state is OPEN with 240 total committed jobs, 1,801,017 cumulative nodes, 125.207 reported cumulative solver seconds, and next_id 253. Final frontier identifiers, in stored order, are 20,19,18,17,16,201,252,251,250,249,248,247,246.

Final state SHA-256: `eb74f9a59a537ee1ac0a7bd9bd3e8dd283c0ca6d5172cc648b6d5aaa6cb6c027`.

All 120 summary receipt hashes, status counts and listed new operation totals agree exactly. Floating-point accumulation was reproduced in the runner's order; rounded seconds above are for reading only.

## Scope

This audit checks transfer preservation, linked native records, domain containment/disjointness and exact state accounting. It does not independently establish that native propagation and branching excluded only impossible assignments or returned every unfinished satisfying assignment. Those coverage claims still rely on the separately reviewed C source and its model premises. The generic Lean capacity argument and source-specific path/geometry results are separate from a kernel-checked native traversal. The remaining frontier proves no exclusion for this full model, and the earlier 120 transitions were preserved and hash-checked rather than re-executed.

## Frozen evidence pins

- `scripts/audit_saved_chain.py`: `eaea0ab9ae159198e47e4e75536d5f9bd9727b56392173e482f478fd76c6e558`
- `scripts/tight_continue.py`: `d219bb4fa1b00f4d5069a98a2e02bdd7ec9f6a8847923c43aae0d5ebaca3fa61`
- `scripts/transfer_frontier.py`: `0bda96748054451c54c8f6c6954a509e16f204501a44db198eb0997f37de1fe3`
- `scripts/tight_solver.c`: `f4cc2de3768b730e3beb0ac152acf25b516cd258c2dfebd8d77155494a745789`
- `data/frontier-transfer.json`: `ca87975effe7404eac60c3ca03405398dd4b3088b7cd54132790cd8b484dbbad`
- `data/search-summary.json`: `05511091196fb05c74d24470f8cb96f71ed2fe5523ea2510ea5883e78d19d661`
- `data/tight-search-progress.json`: `c9f0f39268a807d8038b4c34902080c0c3f05041645ef736eb514a25d62012c6`
- `data/TightPartner214-audit.json`: `07b4e13296d40b3837e5cb7e79807b3ab9c37b5a792675901915c66931e7ad32`
- `logs/tight-engine-review.md`: `4fac5c0058ded576863ec91cc2f5582ee294a2870afafae22207912e52f4b5af`
- `data/chain-audit.json`: `bc6e84a84c8296f2a83340c027c99f68c8f622697dd302efe64787aa4ba7df5f`
