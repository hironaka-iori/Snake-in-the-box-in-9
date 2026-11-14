# Case 23 capacity-chain review

Result: all 100 saved transitions, the complete capacity input, and all required binary inequalities passed independent comparison. The final state remains `OPEN`, with seven pending domain sets. This review establishes native saved-chain consistency; it supplies no Lean traversal certificate or case exclusion. No search, compiler, software test, or process operation was run.

## Input and capacity premises

The saved model has 81 variables, 2,754 binary relations, 120 forbidden assignments, and 120 permutations. The complete input tail was reconstructed byte for byte from these data and `capacity-constraints.json`, including the appended clique declaration and all partner lists. It matches the pinned tail.

The declared mask contains exactly the 32 even six-bit words. The clique has 32 distinct valid variables, each with its domain contained in that mask. The nine covered variables are outside the clique and also have domains contained in the mask. Each partner list has distinct clique members. The declaration agrees with the pinned capacity census and model hash.

The review directly inspected the original binary-table entries for all required inequalities:

- 496 clique pairs, with all 32 equal-word entries forbidden: 15,872 entries checked.
- 198 outside/nonpartner pairs, with all 32 equal-word entries forbidden: 6,336 entries checked.

All 22,208 entries forbid equality. Therefore every satisfying assignment uses each even word once on the clique, and each covered variable must equal a listed partner. These establish the premises of the previously reviewed capacity propagation rules independently of the wrapper's assertions.

## Saved transitions

The initial state is exactly the original model-domain vector with job identifier zero, no receipts, and zero cumulative counters. For every transition, the review checked:

- Exact linkage from the preceding state bytes, before/after hashes, selected final frontier entry, and unchanged engine/model pins.
- Exact input header dimensions and domains, complete input hash, output hash, successful exit, and absence of hard stops or stop reasons.
- Agreement of receipt and output status, node count, solver seconds, and pending count; nonempty contained pending domains and pairwise disjoint returned domain sets.
- Exact reconstructed after-state bytes: removal of the selected job, consecutive identifiers for returned vectors, reversed insertion order, updated counters and status, and the single appended receipt.

The final reconstructed state matches both `state.json` and the saved progress summary. Its bytes remained unchanged through the review. The 100 outputs comprise 88 exhausted subtrees and 12 limited runs; every solution field is null. The first 70 headers use a 10-second limit and the last 30 a 20-second limit; all use a 100,000,000-node limit.

| Cumulative recorded counter | Independently summed value |
|---|---:|
| Nodes | 2,683,356 |
| All removals | 250,774,393 |
| Lexicographic removals | 72 |
| Unique-carrier capacity removals | 2,253,129 |
| Partner-domain removals | 10,136,052 |
| Capacity contradiction returns | 893,000 |
| Solver seconds | 245.655 |

Each output's counters are nonnegative integers, and its three separately counted removal categories sum to at most its total removals. Solver seconds are displayed rounded; exact stored additions and serialization were matched. The native pruning events themselves were not replayed.

## Pins and scope

All seven engine/source pins and four model pins match the current files. The compiler receipt records successful compilation and matching source/binary hashes. The saved Python configuration records `optimize = 0` and enabled assertions; this review did not inspect historical process environments independently.

| Artifact | SHA-256 |
|---|---|
| Initial state | `59682bca085516bfa92cb857fbce7fe2eb72239b766c3e721396ff4186961b28` |
| Final state | `ec3701961111ed7af971295d4512853adaa4f26dc120bc559e70e39b4176d32e` |
| Model | `f016ce4f452b404dd9b539218bddd7ae514e75bff5c901ab15a6a586b9df04d3` |
| Capacity declaration | `b0ff9653b522574b4e51219d355d6337a47039633f4c371333ef95376c72df91` |
| Input tail | `c93b3f9b4cff719e4b471ed96422b3e245e16cbfdb4a43bf2ea150115d2fff1e` |
| Capacity wrapper source | `6aa8325cb39a963d7e21bc6f1f2e720016fedf312f97af5d0b5e21a44b50e67b` |
| Capacity C source | `2a4e12272665b3bcac59a32c64d7167e5e343f1174d0592f5945717e2e0f593e` |
| Capacity executable | `3e83f357b97f84c1287c07b79ccac1bc36def9ce797c170658c6ca4d5dbe6b8e` |
| Python configuration | `f8376c9eea24c470fd9477a2ff10e3dde122d9d8833f6551209d9cdf203a45e7` |
| Progress summary | `736a5de6fadb1a1cc0b9bd0b9cd59d54045ffa28f73e6330c960cf7d8c72995b` |

The implementation's mathematical control-flow assessment remains in `capacity-implementation-review.md`. This review adds direct validation of the actual capacity premises and all saved transition records. Native exhausted-subtree claims still depend on the engine; the complete case has an open frontier and yields no exclusion or upper bound.
