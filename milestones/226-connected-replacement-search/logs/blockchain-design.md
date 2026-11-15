# Second-path block-chain reduction

New worker: `scripts/connected_blockchain.py`, SHA-256 `511ed6cde751886ad0bbb38156e7d2254becade7785a70c3293e99eef3f6d5d2`.

The worker was prepared by source inspection and editing only. It has not been executed, compiled or tested. No runtime improvement or exclusion is established.

## Source provenance and limited change

- Copied predecessor `scripts/connected_pruned.py`: `609726b4d5679e0f1fbb287af7f025b3c5d1508aa5f195be3510964e3f58db80`.
- Original worker `scripts/connected_pairs.py`: `7c1c1dc41c4b7c73ef0038b417f9a09d7068c5b474217ccf272ad2c4b4e4c74a`.
- Exact embedded `bits` and `terminal_blocks` definitions from milestone 194, `scripts/block_bounds.py`: `0d7ae0ae9f9ad12944579bf450dd649dc73e5802749b59ab03ce1d33ffc3b606`.
- Inspected prior application, milestone 224 `scripts/prepare_biconnected.py`: `9181e720f6fed41f1356b3b6d0594601f8371ce4a0ed0971abec136144e3c9f2`.

The implementation embeds the helper definitions unchanged. It uses their anchor-chain vertex mask. It does not use the helper's additional per-block induced-path length bounds or the adjacent-entry/exit reduction applied in milestone 224. Existing workers and checkpoints remain unchanged. Runtime pins include the new worker identity, the two predecessor source hashes, the embedded helper's source hash and the historical application hash. The helper is embedded, so it requires no runtime import from milestone 194.

## Necessary restriction

After every first-path prefix, the second allowed graph still excludes that prefix and its entire closed neighborhood. The original removed-anchor, connectivity, component-size and component-colour checks run first.

The helper finds vertex-biconnected blocks by the ordinary DFS low-link construction, counting a bridge as a two-vertex block. Its incidence graph contains a node for each block and for each original graph vertex. For a connected simple graph this incidence graph is a tree; non-articulation vertex nodes are leaves. The unique route between the second anchors specifies the blocks retained by the reduction.

Every simple path between the two anchors lies in the union of these blocks. A branch outside their incidence-tree route attaches through one articulation vertex. Entering that branch and then continuing toward the other anchor would revisit the same articulation. A simple path cannot do so. If an anchor itself is an articulation vertex, the same argument applies: leaving through a block outside the route would require returning to that anchor. Including all vertices of each retained block gives an overestimate of the vertices an actual path may use, which is sufficient for necessary capacity checks.

The worker therefore rejects a prefix if that retained union has fewer than the prescribed number of second-path vertices or too few vertices of either parity. For width 43, it needs 44 vertices and 22 of each parity. Other supported widths use the alternating counts determined by the second starting anchor. As with the preceding component check, extending the first prefix cannot restore a valid completion rejected at this stage.

When a first path is complete, the second DFS actually uses the retained union as its domain. All ordinary induced-prefix, distance, parity and crossing checks remain. The optional zero-crossing restriction for the first domain, the allocation scope, DFS frontier semantics, and full 193-vertex witness validation are unchanged. No block-chain reduction is applied to the first path.

## Counters and checkpoint scope

`second_domain_prefix_prunes.BLOCKCHAIN_SIZE` and `.BLOCKCHAIN_COLOUR` count additional rejections after every original second-component check passed. These compare the two second-domain capacity criteria; they do not prove that the rejected prefix would survive all subsequent first-path checks in the predecessor worker. `second_blockchain_checks` counts applications after component acceptance. `second_blockchain_vertices_removed_total` sums removed vertices over those applications, so it is not a count of distinct cube vertices.

The second-DFS cache recomputes the same restriction for a complete first path; those cache computations are excluded from the prefix counters. An inconsistent retained mask lacking an anchor raises an error, preserving the current frontier and making no exclusion claim.

Use a fresh tag and a fresh search. Checkpoints from either previous worker fail the new source/worker pin comparison and cannot be resumed under this source. Subsequent checkpoints from this exact new source can be resumed with matching arguments and a fresh tag. `EXHAUSTED` retains the existing distinction between one specified crossing allocation and the whole prepared context. This remains native enumeration without a Lean traversal certificate.
