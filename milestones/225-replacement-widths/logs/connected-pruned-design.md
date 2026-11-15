# Prefix pruning for the second replacement

New source: `scripts/connected_pruned.py`, SHA-256 `609726b4d5679e0f1fbb287af7f025b3c5d1508aa5f195be3510964e3f58db80`.

Original source remains unchanged: `scripts/connected_pairs.py`, SHA-256 `7c1c1dc41c4b7c73ef0038b417f9a09d7068c5b474217ccf272ad2c4b4e4c74a`. The new worker records and checks this provenance pin. Neither the new worker nor a compiler or software test was run during preparation.

For every first-path prefix, the new worker removes that prefix and all its neighbors from the second prepared domain. It rejects the prefix if either second anchor has been removed, if the two anchors are disconnected, if their component has fewer than the required number of vertices, or if either parity class has too few vertices. At width 43 these requirements are 44 vertices, including 22 of each parity. The code computes the corresponding requirements from the width and starting anchor for the other supported widths.

These conditions are necessary. The two replacement intervals are separated in the final path, so every vertex in the second path must differ from, and avoid adjacency to, every first-path vertex. Extending the first prefix only removes additional vertices from the second domain. Any valid second path must therefore lie in the current component containing both second anchors. Its prescribed length requires the stated total size and alternating parity counts. A current shortage cannot be repaired by extending the first prefix.

When `--first-crossings 0` is selected, the first domain is also restricted to the coordinate-8 face containing its first anchor. A path with zero coordinate-8 crossings remains in that face. This restriction is applied only under that explicit allocation argument; unrestricted allocation searches retain both faces.

All other search rules, the two saved DFS frontiers, allocation scope, and complete 193-vertex witness validation are retained from the original worker. Additional counters record prefix rejection for removed anchors, disconnected anchors, insufficient component size, and insufficient parity counts. The source hash and worker identity are included in checkpoint pins. An original-worker checkpoint is rejected by the new worker; a fresh search and fresh output tag are required. Later checkpoints from this same new worker can be resumed with a fresh tag and matching arguments and pins.

The result remains limited to the selected prepared replacement family and any requested crossing allocation. No runtime improvement, new exclusion, or Lean traversal result is claimed by this source preparation.
