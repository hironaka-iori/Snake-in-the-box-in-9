# Round 262 · A 92-site obstruction for an unrestricted partner

At crossing vertex 67, the six unresolved 96-edge parent cases share 92 of their 96 forbidden projected sites. A 95-edge induced path from the crossing cannot avoid those 92 sites, even when every other vertex of the eight-dimensional face is available. This single obstruction therefore excludes a 192-edge join for all six rooted parents. [The 92 normalised vertices and contradiction certificate](groups.json)

For a fixed crossing vertex, translate the crossing to zero and remove it from each projected parent's occupied set. The intersection \(F\) of the resulting forbidden sets is contained in each of them. Any partner compatible with one of the parents must avoid \(F\). Conversely, a 95-edge path avoiding \(F\) would still have to be checked against each full parent to yield a join.

| Crossing in the original labelling | Parent endpoints | Common forbidden vertices | Whole-group conclusion in this round |
|---:|---:|---:|---|
| 1 | 20 | 87 | Open |
| 67 | 6 | 92 | Excluded |
| 161 | 1 | 96 | Open |
| 193 | 9 | 90 | Open |
| 220 | 6 | 92 | Open |

The exclusion uses the established 95-edge rooted-path encoding with equal parity counts, endpoint degrees and face occupancy restrictions. A contradiction was already obtained before any disconnected cycles had to be cut. The proof was trimmed and replayed against the regenerated formula. The other four entries ended at a search limit. [Encoding and replay](masks.py) · [Proof archive](proofs/)

For each of the 262 catalogued 96-edge shapes we next considered both endpoints and all coordinate permutations after translating the endpoint to zero. Exactly 12 of the 524 rooted cases contain an isometric copy of the 92 forbidden sites. Each containing placement has a recorded permutation. No shape in this catalogue meets this particular containment condition at both ends. The obstruction applies equally to a future arm containing these sites at its crossing. [Catalogue and containing placements](transfer.json) · [Containment calculation](transfer.py)

An independent calculation enumerated coordinate maps using sets of vertices of equal Hamming weight. It reproduced the full list of containing placements and rechecked the contradiction certificate. [Independent replay](replay.py) · [Verified totals](replay.json)
