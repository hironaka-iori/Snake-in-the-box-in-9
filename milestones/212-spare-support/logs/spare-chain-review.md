# Complete spare-support chain review

Date: 2026-11-14. Result: all 120 saved transitions reconstruct exactly from the complete original root to the frozen final state. No discrepancy was found. This review reads saved records and recomputes their hashes, set containments and state replacements. It does not run a search, compiler, Lean, software test or process operation.

## Evidence inspected

The initial state has one region, ID 0, containing all 78 original root domains, with zero jobs and an empty receipt list. There are no inherited jobs. For every receipt index 0 through 119, the review independently verified:

- Exact byte continuity between the previous after-state and next before-state; all recorded before/after hashes and job counts agree.
- Selection of the last frontier entry, including its ID and all input domains. Every input has the original 78-variable model dimensions and specifies 3.0 seconds and 100,000,000 nodes.
- The complete header followed by the pinned input tail reproduces the recorded input hash. The exact output bytes reproduce the output hash.
- The original seven engine pins and four model pins agree with every receipt and their actual source/input/executable files.
- All jobs are accepted with exit zero, no hard stop, consistent statuses and counters, no witness, and empty stderr files.
- Every returned region has 78 nonempty domains contained in its selected parent. All 561 pair comparisons among returned regions are disjoint in at least one coordinate. The entire frontier is also pairwise disjoint after each transition, and its region IDs are unique.
- Rebuilding the state by removing the selected region, assigning consecutive IDs to returned regions, appending them in reverse order, updating numeric counters and adding exactly one receipt reproduces every after-state byte for byte. No unrelated field changes.

All 120 receipt files under the case directory are accounted for by the final receipt list. The final reconstruction equals the frozen `state.json` bytes and the parent-provided hash. The final state was reread to confirm it remained unchanged. The saved batch summary has matching engine pins and final-state hash.

## Results and retained coverage

The outputs comprise 104 exhausted subtrees and 16 limited runs. They return 130 regions in total, so the pending count is \(1-120+130=11\). The final state remains OPEN, with 1,051,511 nodes, recorded seconds `76.07700000000004`, and next ID 131. The saved frontier IDs are 20, 19, 18, 17, 16, 102, 130, 129, 128, 127, 126.

| Native counter | Total |
|---|---:|
| Removed domain values | 66,528,748 |
| Lexicographic removals | 18 |
| Support calls | 903,253 |
| Support removals | 63,089 |
| Support failures | 311 |
| Saturated-budget encounters | 100,290 |

These are repeated native operations, without a measured speed comparison. Every recorded startup gate meets the 1 GiB free-memory threshold and reports no resource-query errors or observed Lean processes. Minimum startup free memory is 1,075,666,944 bytes; minimum sampled free memory is 975,745,024 bytes; maximum sampled native private memory is 9,904,128 bytes. No resource stop is recorded. The batch ends at its 120-job budget.

The complete root, necessary support restrictions and unchanged traversal source were separately reviewed in `support-input-review.md` and `support-engine-review.md`. Under those source premises, an exhausted selected subtree contributes no remaining solutions, while a limited subtree retains its unvisited branches in the saved regions. This audit establishes exact replacement, containment and disjointness; it does not independently enumerate every discarded assignment or supply a Lean traversal certificate. Eleven regions remain open, so no case exclusion or new global bound follows.

## SHA-256 pins

Paths are relative to `E:/Snake-in-a-box/milestones/212-spare-support/`.

| Artifact | SHA-256 |
|---|---|
| `data/case-22/initial-state.json` | `e9d52f433edd04b330bb7f08cae46a865b231c7d599a25dae005b96dae103334` |
| `data/case-22/state.json` | `6a2090ba3a2af9561461bf7ff5f6ef133996a25c13dbc32d48f74d29b2aa90a8` |
| `data/case-22/input-tail.txt` | `a6d93cdaac4436edd25781756128a569e71cd61ee350fd4745d58eed3bbb9689` |
| `scripts/spare_solver.c` | `4c1d8c773075ad6b04c05125b7e5b7fb27b26cdbe9c77e6a9be8d2202700acf0` |
| `scripts/spare_continue.py` | `15514247092ebcfea8abac7516be09f45f6bb75db0c49edf304e521c94a56d89` |
| `build/spare_solver.exe` | `2702a937633af9203e7c64f3bdf3c9546c14ea3590ea46dc1e643d334030ac53` |
| `data/spare-batch-1794664496182060500.json` | `c0efdf1fc0b9e351562e7bd61990121706f180887a99ee5df72fa1e773c89ebd` |
| `data/case-22/run-119-1794664495732450700/receipt.json` | `7c147ca84d2fa3aaabce25efda0a4d18b066816421fd5d3e13e7a52380829ce8` |
| `logs/support-engine-review.md` | `6e6903b0a0150e34586f7163547fe3db0f76e88d5d3a6ac776b677f4452ffc72` |
| `logs/support-input-review.md` | `6e1a1daf58c1282c7f5d6cbdd949d3bcd331dbd720fc01eacca933c64ac807fe` |
