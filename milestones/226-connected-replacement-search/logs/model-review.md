# Round 226 checkpoint, block-chain and crossing-split review

Conclusion: no invalid exclusion or lost search branch was identified in the reviewed changes. The checkpoint transfer preserves the original search state. The block-chain mask is a necessary restriction for the second path. Both ordinary width-43 allocation batches are now terminal and exclude their same 24 contexts natively. Exceptional context 114 is outside both batches and requires its distinct allocation (0,1).

This was a mathematical and source review, with read-only JSON comparison, exact geometry arithmetic and file hashing. No worker, solver, compiler or software test was run. Only this review file was written.

## Sources and hashes

Read all 424 lines of `scripts/connected_blockchain.py`, its complete diff against the byte-identical round-225 predecessor, all 34 lines of `logs/blockchain-design.md`, all 82 lines of `scripts/joint_split.py`, and all 58 lines of each execution wrapper `run_split.py` and `run_pruned.py`. Read the complete historical `bits` and `terminal_blocks` function definitions in milestone 194 and the complete milestone-224 application `prepare_biconnected.py`. The unchanged predecessor has the separate full-source review in round 225, `logs/connected-model-review.md`.

| Artifact | SHA256 |
|---|---|
| `scripts/connected_blockchain.py` | `511ed6cde751886ad0bbb38156e7d2254becade7785a70c3293e99eef3f6d5d2` |
| `scripts/connected_pruned.py` | `609726b4d5679e0f1fbb287af7f025b3c5d1508aa5f195be3510964e3f58db80` |
| `scripts/connected_pairs.py` | `7c1c1dc41c4b7c73ef0038b417f9a09d7068c5b474217ccf272ad2c4b4e4c74a` |
| `scripts/joint_split.py` | `9ac7754057fabcba0ef0c2e9c61fdd4834e78b8a3bab2a61cd3dfdba7dda1cf9` |
| `scripts/run_split.py` | `dd4ac974a0be544b76ce95569026f2214d9d1e5cb84e5b2670701792b340ab1f` |
| `logs/blockchain-design.md` | `12e15dfe0355215d53b3af8bc8fd3171d830834fc1d96d21b4526f14c55a397c` |
| `data/regions43.json` | `b1cf54d596bcd8e04162fef9741dca90eed03ab03e78089318614215d1b9b3da` |
| `data/checkpoint-transfer.json` | `348530c6cb31efa764aedf8d274b7fbf8d5c68bc7c7379bff31f14eaf6201a44` |

## Checkpoint transfer

The original round-225 `pruned43-22-zero/checkpoint.json` hashes to `6777944b1c9562355c9e09a4ca258bf0da33900007b93619037c5e716c0aa1ba`. The transferred checkpoint hashes to `28c3530c14e63f97caf55c0a3c98680df29f0381f42fc73e505e3a2ed75dd657`. Both match the transfer record.

A recursive comparison of the complete decoded records finds exactly one changed field: `pins.source` changes from the round-225 absolute input path to the round-226 absolute input path. The two input files are byte-identical. All eight files listed in `copied_files` match their saved hashes and the corresponding round-225 bytes, including both workers and the original execution wrapper.

Every state field, count, allocation, timing value and source hash is unchanged. The 20 pending first-prefix lengths are 3, 3, 4, 6, 8, 8, 12, 13, 13, 15, 20, 21, 22, 23, 23, 23, 23, 26, 27, 27, exactly as recorded. This preserves the unfinished context-22 allocation (0,2) search; it does not establish exhaustion. The relinked checkpoint remains a checkpoint for `connected_pruned.py`. It is not a checkpoint for the new block-chain worker.

## Block-chain necessity and implementation

The embedded `bits` and `terminal_blocks` functions are text-identical to the definitions in `194-targeted-extensions/scripts/block_bounds.py`, whose full-file hash is `0d7ae0ae9f9ad12944579bf450dd649dc73e5802749b59ab03ce1d33ffc3b606`. The historical milestone-224 application hash is `9181e720f6fed41f1356b3b6d0594601f8371ce4a0ed0971abec136144e3c9f2`, matching the new provenance constant.

The helper's DFS low-link decomposition treats bridges as two-vertex blocks. On the connected component of the first anchor, the incidence graph between block nodes and original vertices is a tree, with non-articulation vertices as leaves. The path between the two distinct anchors in this tree determines the retained blocks. Distinctness is supplied here by the positive-width intervals and the induced seed; the helper's degenerate equal-anchor case is not used.

Every simple path between the anchors lies in the union of the retained blocks. A component attached away from their incidence-tree route can only be entered and left through the same articulation vertex, contradicting simplicity. This also handles an anchor that is itself an articulation vertex. Retaining every vertex of a block on the route gives a superset of possible path vertices, which is sufficient for upper capacity checks.

For each first prefix, any compatible second path avoids the prefix and all of its neighbours. A completed first path can only remove additional vertices. The new check therefore correctly rejects a prefix when the anchor-chain union has fewer than the required second-path vertices or insufficient vertices of either cube parity. For width 43, the requirements are 44 vertices and 22 of each parity. The general formulas give the alternating colour counts for every supported width. These are necessary conditions, with no sufficiency claim.

The new worker uses only `chain['mask']`. It does not use the helper's computed `upper_edges`, the per-block length estimates, or milestone 224's additional adjacent-entry/exit deletion. Consequently those stronger historical deductions are not dependencies of this change. At a complete first path, restricting the actual second DFS to the same block-chain mask also preserves every compatible path. The block-chain reduction is applied only to the second path.

The source diff leaves induced-prefix expansion, distance and parity checks, the crossing budget, the optional zero-crossing first-face restriction, cross-path separation, and the full 193-vertex witness audit unchanged. A complete first path stays on the first frontier until its entire second frontier is exhausted. The second-domain cache is reconstructed from that pending first path after resumption. New masks are computed before the corresponding frontier is discarded; a helper failure raises an error rather than certifying exclusion.

Worker identity and source pins prevent silently resuming either predecessor checkpoint under the new algorithm. A new block-chain search must begin fresh; its own subsequent checkpoints may resume with identical source/input/arguments. `EXHAUSTED` still distinguishes a specified allocation from a whole prepared context. An unfinished or failed run supplies no exclusion. The existing narrow interruption edge case, where an empty frontier can be saved before the exhaustion status assignment, affects resumability rather than validity of an exclusion and is unchanged from the previous review.

The design note correctly limits the new counters. Block-chain rejection counts are additional failures after the old second-component checks; they do not show that a prefix would pass all later first-path checks. Removed vertices are summed across checks and are not distinct cube vertices. No runtime improvement or traversal certificate follows from this source review.

## Exact width-43 allocation coverage

The 25 unresolved IDs in the immutable round-225 result are:

`22–29, 64–71, 106–114`.

For every one, direct arithmetic on the literal anchors gives first-pair coordinate-8 disagreement zero. For the 24 IDs `22–29, 64–71, 106–113`, the second-pair disagreement is also zero and the replacement crossing budget is two. Thus exactly (0,2) and (2,0) are possible. These are the same 24 distinct IDs listed in both round-226 split arguments; neither batch includes 114.

Context 114 has intervals [2,45] and [131,174], anchors (17,104) and (35,462), endpoint disagreements zero and one, and replacement budget one. Its only possible allocation is (0,1). Applying the ordinary two-allocation conclusion to this context would be incorrect; the reviewed batch selection avoids that error.

The split model retains the original necessary constraints: selected anchors; exactly 44 vertices per path; selected degree one at anchors and two elsewhere; exact cube-parity counts; Boolean vertical-edge products; per-path crossing parity; the combined crossing budget; and every cross-path equality or adjacency conflict. Cycle-component cuts exclude complete selected cycles, which an induced path cannot contain. Witness extraction is followed by the complete all-pairs, cardinality and crossing audit. The only source change from round 225 is clarification of the saved scope string to the actual requested IDs.

## Terminal split outcomes

Both receipts are now `ACCEPTED_NATIVE_RESULT`, exit code zero, with no stop reason. Each result reports complete coverage of precisely the same 24 IDs and 24 `INFEASIBLE` records. No cycle cuts were added in either batch. Recomputed hashes match their saved worker/input pins, result pins and every exported per-query model pin. The zero-allocation stdout/stderr pins also match.

| Result or receipt | SHA256 |
|---|---|
| `data/split43-two.json` | `8fc54f0c42252f8638bbc29f688a3450d757b8e37c63e31ef1765dfa4902fb03` |
| `data/split43-two-execution.json` | `68d3f848efafce6cece147a5affa15666651c04585d4aa932bd177f996f6a572` |
| `data/split43-zero.json` | `9cf937a1c0fa52927065ad53874c419d6f7813ad2afe988e9bd5ef281b09fc8c` |
| `data/split43-zero-execution.json` | `5b5e1254eac98f5bf5c04c7e0c66b10d84fa8ce784287027634935773bfcb3b6` |

Together these records exclude the 24 ordinary contexts within the fixed construction family. They leave context 114 outside their coverage. No outcome for a separate context-114 query is included in this review. The native exclusions have no Lean contradiction certificate, and the block-chain search has no Lean traversal certificate. No new snake or global upper bound is established.
