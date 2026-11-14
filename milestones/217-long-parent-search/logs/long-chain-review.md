# Round 217 long-budget saved-chain review

Result: PASS_SAVED_TRANSFER_AND_NEW_TRANSITIONS. Independent audit of frozen research records on 15 November 2026. The audit ran only after the parent confirmed native session 38974 was terminal with exit 0 and no search lock. No solver, compiler, software tests, or new search was run.

## Baseline, unchanged engine and transfer

Round 216 has a version 2 local ledger: 400 jobs, 2,044,830 nodes and 236.214 reported solver seconds. Its pinned summary includes the earlier baseline and gives 1,140 cumulative jobs, 6,496,107 nodes and 658.343 seconds. The round 217 history_parent correctly takes those cumulative values from the summary. It does not mistake the 400 local jobs for the full history.

Verified the source state, source-summary hash, prior chain-audit hash and matching local/cumulative arithmetic. Checked 415 selected entries from the pinned source publication manifest, including all 400 source receipt hashes, the source state and initial state, summary, audit, engine files and model files. Prior audit source pins also match. The declared publication reference cfa2e8ed386259be99cd2564361591cd92a3b7bc is retained; its Git commit tree was not separately inspected.

The new initial state reconstructs byte-for-byte by resetting local jobs/nodes/time and receipts and replacing the linked history_parent. All nine transferred vectors, order, identifiers, next_id 1149, four model-file pins, status, index, version and counter scope are preserved. The copied source-state snapshot and four model files equal their source bytes.

All old and new engine pins are identical, including driver, native source and executable. The reused round 216 compiler receipt, source review, and four Lean receipts (TwoStep216, Joint216, PathJoint216, LiteralJoint216) match their saved hashes. The proof sources, objects, logs and dependencies were checked against those receipts. No new compilation or proof check is claimed.

Source-state SHA-256: `4599f3f699d81ee7e14295d537715d621db8a9bb5584ea8a9121d4f2ed592480`.

Transferred initial-state SHA-256: `1a88353afd4ef3d257e4bb86957550ea49e6774ee5b4bc2187e6d33f29337c61`.

## Reconstruction of all 120 new transitions

Every accepted transition matches the runner semantics exactly: prior-state bytes and hash; selected last frontier entry; nonempty root-contained input domains; serialized input header and input-tail hash; receipt/source/model/stdout pins; successful exit and empty stderr; returned-region status, counts and counters; and exact subsequent state serialization.

Each returned region is contained in its submitted region. Returned sibling regions are pairwise disjoint, checked over 486 pairs. The initial and all successor frontiers are also pairwise disjoint, checked over 3,251 pairs. Children receive fresh consecutive identifiers in returned order and are appended in reverse order after removing only the selected final entry. Untouched regions, history_parent, version and counter scope remain unchanged. All 120 state-after hashes link to the next state-before bytes, ending in the final saved state. There are no missing, duplicate or extra uncommitted receipts.

All 120 inputs use 30.0 seconds and 100,000,000 nodes. Every startup gate records no other Lean process or query error. Minimum recorded startup free memory is 2,109,816,832 bytes; minimum sampled free memory is 1,952,387,072 bytes; maximum recorded native private memory is 9,928,704 bytes. No resource stop or hard stop is recorded. These are saved observations, without an independent historical process trace.

## Which transferred regions are finished

Assigned each transferred region its original identifier, then propagated that identifier to every returned child through the exact state reconstruction. A transferred region is classified below as exhausted only when all its recorded descendants have disappeared through accepted native transitions. This is a conclusion about the native ledger, conditional on the implementation's propagation and traversal correctness.

| Transferred ancestor | Local jobs | Local nodes | Solver seconds | Remaining descendants |
|---:|---:|---:|---:|---|
| 20 | 0 | 0 | 0.000 | 20 |
| 1138 | 33 | 1,481,727 | 165.513 | 1254, 1267, 1266, 1265, 1264, 1263, 1262 |
| 1137 | 66 | 2,741,545 | 310.469 | None; exhausted in the native ledger |
| 1136 | 13 | 731,340 | 82.250 | None; exhausted in the native ledger |
| 1135 | 4 | 271,320 | 30.047 | None; exhausted in the native ledger |
| 1148 | 1 | 1,596 | 0.187 | None; exhausted in the native ledger |
| 1147 | 1 | 946 | 0.109 | None; exhausted in the native ledger |
| 1146 | 1 | 27 | 0.015 | None; exhausted in the native ledger |
| 1145 | 1 | 1 | 0.000 | None; exhausted in the native ledger |

Seven transferred ancestors are exhausted according to this ledger: 1137, 1136, 1135, 1148, 1147, 1146, 1145. Ancestor 20 was untouched and remains pending. Ancestor 1138 remains open through seven pending descendants. Thus the eight current frontier entries belong to only two of the original nine regions.

## Totals and final state

The 120 local jobs comprise 106 exhausted subregions and 14 limited runs, with no witness. They record 5,228,502 nodes and 588.590 solver seconds, returning 119 unfinished regions. The frontier accounting is nine transferred regions minus 120 submitted regions plus 119 returned regions, leaving eight.

The cumulative summary correctly adds the pinned baseline: 1,260 jobs, 11,724,609 nodes and 1,246.933 reported solver seconds. search-summary.json and joint-search-progress.json agree with the reconstructed local state, counters and all 120 receipt hashes. The run stopped at its job budget.

The final state is OPEN. Its frontier identifiers are 20, 1254, 1267, 1266, 1265, 1264, 1263, 1262, and next_id is 1268. Final state SHA-256: `79d48c05cfc33461671656122c3fa003b2488cc344fc6adf89dd532fb6502452`.

All operation totals were independently summed from stdout and compared with the summary; full figures are preserved in chain-audit.json. They include 538,464,093 recorded domain-removal operations, 55,944,396 word-subset removals, 388,960 partner tight-set removals, and 1,334,293 joint-pair removals across 25,384 examined triples and 334 joint sweeps. Joint new relations remain zero. Repeated operations do not count distinct globally excluded assignments. This batch supplies no controlled performance comparison.

Floating-point additions were reproduced in the runner's order; displayed decimal seconds are rounded. The final state and pinned source state/summary were checked again after reconstruction and remained unchanged.

## Limits

This audit verifies the linked baseline, copied data, saved transitions, frontier ancestry and exact accounting. It does not independently prove that C propagation discards only impossible assignments or that all unfinished satisfying assignments appear in returned regions. Full native traversal certification remains separate from the reviewed implementation and the generic/path Lean results. The seven finished ancestors have native-ledger evidence, while two ancestor regions remain open; this complete model has not been excluded.

## Frozen evidence pins

- `scripts/audit_saved_chain.py`: `47949e6d09fa3621d9a73e90c783dfcac509d3406fe7033bb8440420cb776f3d`
- `scripts/joint_continue.py`: `0f464816a4f862a6482966cab8f70f12e7b2b4afdabcd882d9f0bc0aeadacb36`
- `scripts/transfer_frontier.py`: `7cbc65be81c33bb0471a8e127f3ac2b451d84694da5761d370f8db9b1d30037d`
- `scripts/joint_solver.c`: `6d025faf3620933ceaab7fd12c5d180f1c1bd6142e67de53950012fb162b1e91`
- `scripts/summarize_search.py`: `48ec1b43b1b8aa2126c24bb934f7aa82c66b290571ad14d9245d1692a742b23e`
- `data/frontier-transfer.json`: `01bb2761fa82d90073b7858d2648cc553a9dea42598e26af707fb81d9ff9b33c`
- `data/search-summary.json`: `d2e81d1d55819493257e3e8e475ceff94ce2d5f79d7890eb03d4d95775c9b97b`
- `data/joint-search-progress.json`: `d2d1a79fd2ac473b419533f010836a1b814d35b9690d90d88148c9d2a7ca7c29`
- `data/chain-audit.json`: `b4c8c3f506a9777683a035d1b5c1783a1daf4fc2abe162535f3291078295e9bd`
