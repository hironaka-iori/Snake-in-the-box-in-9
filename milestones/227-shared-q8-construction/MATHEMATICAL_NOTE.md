# Round 227: fixed upper portions and lower-dimensional replacement tasks

All 301 maximal width-44 contexts of the selected endpoint-24 construction are now computationally excluded. This completes the exclusion for two length-preserving replacement blocks of at most 44 edges each. There is no new snake or global upper bound. The goal is to be paused after publication at the user's request.

## Construction and scope

The original normalized bank-123 path has 191 edges, endpoints 0 and 88, and four crossings of coordinate 8. Appending endpoint 24 requires changing the original vertices at indices 7 and 143. Two open index intervals may change while their anchors, outside positions and edge lengths remain fixed. The desired complete path has 193 vertices and four coordinate-8 crossings.

For width 44 the maximal intervals are [a,a+44], a=0,...,6, and [c,c+44], c=100,...,142. There are 301 pairs. Any smaller allowed replacement can be padded by unchanged original positions into a maximal pair. The preceding round excluded 259 and left 42 unresolved. This round excludes those 42 by a lower-dimensional reduction. Other seeds, endpoints, more replacement regions and changes of block length are outside this conclusion.

## Why the reduction is valid

A path with exactly two coordinate crossings, starting and ending in the upper face, has three contiguous pieces: an upper prefix A, a lower path B and an upper suffix C. Each piece is induced. A and C must be disjoint and nonadjacent. Between opposite faces, adjacency is equality of the lower projections. Thus B may meet the upper projections only at the two prescribed joining pairs. These conditions also suffice: every vertex pair is either within a piece or is covered by one of the stated separation conditions.

A separate lower path P is disjoint and nonadjacent to the second replacement exactly when P and B are disjoint and nonadjacent and P avoids every projection of A and C. If the complete second replacement has 44 edges, then B has 44-|A|-|C| edges, with the bars counting vertices. A one-crossing replacement has only one upper piece and the analogous formula. Fixing the small upper pieces therefore leaves two induced-path problems in Q8 with explicit endpoints, lengths and allowed domains.

The general actual-path construction already exists in accepted `TwoCrossings188`; endpoint parity, constant-face capacity, residual containment and simultaneous replacement also have accepted earlier Lean receipts. The new finite enumeration is an instantiation with separate native obligations. The complete numerical exclusion is not a new universal theorem for Q9.

## Seven contexts reduce to five tasks

The first lower path has 43 edges from 18 to 224 and is followed by 480. The second upper domain has 13 or 14 vertices. Enumerating all separated induced upper prefixes and suffixes gives 18 configurations. Comparing both endpoint pairs, lengths and literal domains gives six exact groups. One is contained in another: configuration 17 has configuration 0's domains with vertex 212 removed from each. Five tasks suffice:

| First lower endpoints and edges | Second lower endpoints and edges | Domain sizes before mandatory-anchor pruning |
|---|---|---|
| 18 to 224, 43 | 35 to 201, 33 | 107, 106 |
| 18 to 224, 43 | 35 to 208, 32 | 107, 106 |
| 18 to 224, 43 | 35 to 212, 39 | 107, 106 |
| 18 to 224, 43 | 35 to 208, 38 | 106, 105 |
| 18 to 224, 43 | 35 to 201, 35 | 105, 104 |

All five reduced queries are natively infeasible. The alternate first suffix through port 232 retains its separate exclusion from round 226. Together these exclude contexts 194,195,196,197,198,199,201.

The first two task groups occur in all seven contexts. Symbolic substitution shows that the same lower paths reconstruct the identical full 193-entry sequence across each group. The contexts differ only in where their interval boundaries divide unchanged upper vertices. This is a redundancy of the construction representation; it does not establish a new cube symmetry or a symmetry of every snake.

## The other 35 contexts

Both first anchors lie in the lower face, so their crossing count is even. With total replacement budget one, the allocation must be (0,1). With budget two, the second anchors are upper and their upper domain has fewer than the required 45 vertices. The second cannot have zero crossings, so the allocation must be (0,2). In every case the first path remains entirely in Q8 and has 44 edges.

The second path has four upper-to-lower contexts, two lower-to-upper contexts, and 29 upper-to-upper contexts. Complete upper enumeration gives 230 configurations, 79 exact groups, and 52 representatives after strict domain containment. All 52 reduced queries are natively infeasible. Every query in both batches terminates infeasible at its first solve, with no cycle cuts. The full mapping from configurations to representatives and from representatives to contexts is retained in `data/coverage44.json`.

The selected-vertex model requires exact path size and colour counts, selected endpoint degree one, other selected degrees two, and mutual disjointness/nonadjacency. It permits an endpoint path plus disconnected cycles. Every intended pair satisfies this relaxation, so its infeasibility excludes the pair. This remains a native solver conclusion without a Lean contradiction certificate.

## Direct enumeration and verification limits

Before solving the reduced models, a two-minute common-prefix enumeration processed 5,157,314 first prefixes. It found no complete first path passing the companion checks and ended at its time limit with 14 pending first prefixes. This is not exhaustion. Its checkpoint is retained but superseded by the complete native cover.

Review identified an interruption-sensitive frontier update in the original worker. Its actual run ended normally at a loop-boundary time limit, so that saved frontier was unaffected. The atomic successor changes only state-update handling, and the transferred checkpoint changes only the worker hash. Neither the successor nor the transferred frontier was run. Interrupted checkpoints from the original worker must not support resumed exhaustion.

The new concrete Lean facts cover the 35 crossing/face premises, exact equalities of the two seven-member task groups, and the domain containment of configuration 17 in 0. Their extraction from JSON remains native. Upper enumeration, prepared-domain necessity, complete coverage assembly and all 57 solver contradictions are independently reviewed native work. No software tests were created or run. Accepted compiler receipts, source hashes, execution receipts and manuscript verification are recorded at publication.

## Frontier at the pause

The selected two-block route is closed through width 44. An unchanged query or the superseded shared DFS frontier should not be resumed. The smallest continuation is to prepare width 45 and apply the upper-portion reduction before launching long searches. A different endpoint or seed, or a construction with different crossing allocation, changes the family more substantially and may be preferable if wider intervals reproduce the same reduced tasks. Equal full-sequence templates should be removed before counting ostensibly different contexts.

The first constructive target remains a verified 192-edge snake; 196 remains a conjectural target without a witness. Coworkers handle global upper bounds. The maintained interval stays 191 to 233, with the independent rebuild of the contributor's 233 assembly pending. Both manuscripts, all raw local models, their exact compressed archive, and the paused continuation record are retained.
