# Continued cases 24 and 9: saved-chain review

Result: all requested byte and transition comparisons passed. Each case contains the unchanged 100-transition prefix from `milestones/208-resumable-history`, followed by 50 new accepted transitions in `milestones/209-slice-capacity`. Both current states remain `OPEN`. No search, compilation, software test, or process operation was performed; case 23 was not audited.

## Checkpoints and inherited evidence

For each case, the frozen milestone 208 `state.json` equals both the copied transition-99 `state-after.json` and the new transition-100 `state-before.json`, byte for byte. Its ordered 100-receipt list equals the first 100 entries of the final 150-receipt list.

All files in those 100 inherited run directories were compared with their milestone 208 counterparts: 600 files per case, 1,200 total. The filenames and bytes all agree, including every inherited receipt, input header, output, error log, and before/after state. The original `initial-state.json`, model, permutations, and input tail also agree byte for byte. All six pinned engine/source files agree with both the saved pins and the milestone 208 files.

| Case | Frozen state after 100 transitions | Current state after 150 transitions |
|---|---|---|
| 24 | `833ca39676a024c245971b7d9d714a4990164121a78f9e09d5144a9b6c78fcfa` | `e35e024400554a7d69a481700d8aee3dd858c0828b9a00d414ca6883526b3795` |
| 9 | `4d57547675175d726ed112c23cb3bc7c623f1e0735132b635796db382b5ee3f6` | `51d429a7bf57aab2fc7f80e4b59b8ecac1318282f7ec704b14a593b087755fad` |

## All 100 new transitions

The review independently reconstructed the saved-data transformation for each new transition, in receipt order:

1. The before-state bytes equal the preceding after-state bytes and the receipt's before-state hash. The selected job is the last frontier entry, with the recorded job identifier.
2. The input header exactly contains the model dimensions, the recorded domain vector, a 20-second budget, and a 100,000,000-node limit. The complete original input tail was reconstructed from the model's binary tables, forbidden assignments, and permutations. The concatenated header/tail hash matches the receipt.
3. The receipt records successful exit, no hard stop, no stop reason, unchanged engine/model pins, and `ACCEPTED_TRANSITION`. Its output hash, solver status, node count, elapsed solver time, and returned-frontier count match the saved output.
4. Every returned domain vector has the required dimension, nonempty domains, and componentwise containment in the selected job. Distinct returned vectors describe disjoint assignments. `LIMIT` outputs have a nonempty pending list; `EXHAUSTED` outputs have none. Every output has a null solution.
5. The expected after-state removes exactly the selected last job, allocates consecutive identifiers to returned vectors, appends them in reverse order, increments the counters, appends exactly one receipt, and sets the status from the resulting frontier. The entire reconstructed JSON byte sequence equals the saved after-state, including the receipt's after-state hash.
6. The last after-state equals the current state byte for byte. Both frozen and current state files remained unchanged across the review.

No discrepancy was found.

| Case | New transitions | New subtree `EXHAUSTED` | New `LIMIT` | New nodes | Added solver seconds | Pending before / after | Final status |
|---|---:|---:|---:|---:|---:|---:|---|
| 24 | 50 | 44 | 6 | 6,195,823 | 188.314 | 5 / 8 | `OPEN` |
| 9 | 50 | 45 | 5 | 4,965,457 | 154.175 | 6 / 3 | `OPEN` |

Final cumulative node counts are 9,625,900 and 8,142,891 respectively. Solver seconds are displayed to three decimal places; the exact stored floating-point additions and serialization were also matched.

## Engine and model pins

The same engine serves both cases. Each following file was hashed in milestone 209 and compared byte for byte with milestone 208.

| Relative file | SHA-256 |
|---|---|
| `scripts/continue_search.py` | `78641f36dddce1299c6e3953ae1caaf682cc374f7888c4c43722e4e1ef1e786d` |
| `scripts/history_solver.c` | `5de5aa76686e3cf804da7d6d9dbb2a4202ac44442c5cc1e11fe9a0054cb5f764` |
| `scripts/history_model.py` | `e96cea7d793be2e77022c784179d29ce82f2f5c4cbb51c1840d6dc90deb9ae41` |
| `scripts/native_resources.py` | `2e9e7d499ef7068d10d7ca7e31c9a9dc7ef19abb72b0396d3eab9824376b4413` |
| `build/history_solver.exe` | `4e4e89fe7a1e21c106dc527ee09e2e4c243e6d9f2f2496a4b2258d51caf808c8` |
| `data/lower-dimensional-input.json` | `d62c92cc97eae196b21aeefe2111adfb03cc3121b9b62ba7e3e2c6ee6920c20d` |

| File | Case 24 SHA-256 | Case 9 SHA-256 |
|---|---|---|
| `model.json` | `23b75b3fc57e53bbbdb563732fed1c4034a27d50a1fb9e09f7df25bd542ea068` | `fbf0e20edc2c76c5417bc16c8ad9101d319ad605314a0751ad2a31491975bf97` |
| `input-tail.txt` | `fbf41c8d13567db38d28f1a76efe7b44a3abd349be5d2a589391b387ea65aef1` | `ef2e32944ead2ac20fed001020dee3778af86b52385dac87a820a4a4caa71124` |
| `initial-state.json` | `5160d3ac624c0417515f0ce518e76425cc1c2089d1203da846515ec612a3e466` | `197c2bbfc87e296caa605c698c4908202d6aa1d8e6ddc727a51e98ca3697eb0b` |

Both permutation files have SHA-256 `7e4e3dde90085bc5365ae29d2af69af62281fe52d69ea73482e4ef257a0abb93`.

## Scope

This review establishes preservation of the frozen evidence and exact consistency of the 100 new saved transitions. It does not repeat the original milestone 208 mathematical traversal audit or independently certify the native solver's exhausted subtrees. Both complete case frontiers remain open, so neither case is excluded. No upper-bound conclusion follows.
