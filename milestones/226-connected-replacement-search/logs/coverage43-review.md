# Round 226 complete width-43 cover and width-44 trimming review

Conclusion: the saved records cover all 294 maximal width-43 contexts with native exclusions. The two first-edge queries correctly close the final context 114. The proposed width-44 boundary-omission condition is necessary for actual candidates, conditional on this restricted width-43 exclusion. Neither conclusion is a global snake bound or a Lean-certified solver contradiction.

## Final first-edge cover

Read the complete `first-edge-cover.json`, all 84 lines of `scripts/joint_first_edge.py`, its complete diff from the previously reviewed allocation worker, and both terminal result/receipt pairs. Read the resulting `coverage43.json` and independently reconstructed its set coverage from the prior result and new exclusions.

The literal first domain for context 114 has anchor 17, other anchor 104, and exactly two cube neighbours of 17: 19 and 49. Both are in the anchor's coordinate-8 face. This independently reproduces the saved child list. Endpoint parity and the total replacement budget one force allocation (0,1), so every actual first replacement is covered by one of these two choices.

The source adds exactly a first-neighbour argument, its membership/adjacency assertion, the selected-vertex equality, and a scope clarification. Existing degree, cardinality, parity, crossing, compatibility and cycle conditions are unchanged. Since the selected starting anchor has exactly one selected neighbour within its replacement, selecting 19 or 49 forces that vertex to be the first vertex after the anchor in an actual path. No arbitrary interior-position assumption is imposed.

The exported model for neighbour 19 has variable `x0_19` at index 4 and an unconditional singleton linear row with coefficient one and domain [1,1]. The neighbour-49 model has the corresponding row for `x0_49` at index 12. Thus the saved model bytes contain the asserted branch conditions.

Both receipts are `ACCEPTED_NATIVE_RESULT`, exit zero, with no stop reason. Each result contains exactly context 114 and one `INFEASIBLE` solver iteration, with no added cycle cut and no witness. Source/input/model/result/log hashes agree with the saved pins. Their solver times are approximately 0.945 and 1.063 seconds; these are terminal infeasibility results, not timeouts.

## Complete context accounting

The unchanged round-225 `pair43.json` has 294 distinct IDs: 211 inherited exclusions, 58 direct infeasible results and 25 unknown results. The prior 269 excluded IDs are disjoint from the 24 IDs covered by both crossing-allocation batches:

`22–29, 64–71, 106–113`.

The remaining ID is 114, now covered by first neighbours 19 and 49 under its only allocation (0,1). The union is exactly IDs 0 through 293, with no omission or duplicate context counted toward the total:

\[
211+58+24+1=294.
\]

`coverage43.json` has the same complete ID set and every saved pin matches. Its `combined_status` values give 211 inherited, 58 initial infeasible and 25 cover-excluded contexts. Original `status: UNKNOWN` fields are retained as the historical initial outcomes; they are not the final combined classification.

The implication for blocks of at most 43 edges uses the previously reviewed enlargement coverage. It concerns the fixed seed, fixed outside positions, original anchors at the chosen interval ends, appended endpoint 24, equal-length replacements and four coordinate-8 crossings. The domain interpretation and all inherited native exclusions retain their separately stated audit limitations. Incomplete direct-search checkpoints do not participate in this exclusion proof.

## Necessary width-44 boundary omission

Consider an actual candidate on maximal 44-edge intervals [a,b] and [c,d], with b=a+44 and d=c+44. Its complete indexed path agrees with the original seed outside the two open intervals. Let the original first-block boundary-adjacent vertices be \(p_{a+1}\) and \(p_{b-1}\), and analogously \(p_{c+1},p_{d-1}\) for the second block.

If \(p_{a+1}\) is in the first replacement's selected set, it is adjacent to its retained anchor \(p_a\). The replacement is induced and its anchor has degree one within the replacement. Therefore its first step is necessarily to \(p_{a+1}\), giving \(q_{a+1}=p_{a+1}\). Conversely this equality implies selection. The same argument at the right anchor gives equivalence between selecting \(p_{b-1}\) and the equality \(q_{b-1}=p_{b-1}\). The equivalences also hold for the second block. They use inducedness or the corresponding selected-degree condition; selection alone in an arbitrary noninduced path would be insufficient.

Selecting a left boundary neighbour allows the interval to be trimmed to [a+1,b]; selecting a right boundary neighbour allows trimming to [a,b-1]. The complete candidate is unchanged. The newly exposed anchor equals the original seed vertex at its index, while the old anchor is now part of the retained outside segment. Thus the anchor requirement of the smaller context is preserved even though the interval's endpoint index changes. Each resulting interval has 43 edges and outside agreement is retained.

The blockers remain strictly inside the trimmed intervals. In the saved seed, \(p_7=28\) and \(p_{143}=56\), and both are adjacent to the final appended endpoint 24. The unchanged preceding endpoint is \(p_{191}=88\), distinct from both. An induced candidate ending in 88,24 therefore cannot select 28 or 56 anywhere earlier. Any trimming that would move blocker index 7 or 143 onto a new retained anchor would require selecting exactly that forbidden blocker, which is impossible.

The maximal index ranges also remain correct. For width 44 they are 0 <= a <= 6 and 100 <= c <= 142. A valid left trim of the first interval has a+1 <= 6, because a=6 would expose blocker 7. A valid right trim leaves a unchanged. For the second interval, left trimming gives c+1 >= 101 and cannot give 143, while right trimming requires c >= 101 because c=100 would expose blocker 143 at d-1. Thus the trimmed pair belongs to the enumerated width-43 ranges 0 <= a' <= 6 and 101 <= c' <= 142. Disjointness is retained. Path length, endpoint 24, and the total crossing count are unchanged; the allocation between replacement and retained edges may change, which is allowed by the width-43 family.

Consequently, if each width-44 block selected at least one of its own two original boundary-adjacent vertices, each could be trimmed by one edge, producing a member of the excluded width-43 family. Every remaining actual width-44 candidate must therefore have at least one block omitting both of its boundary-adjacent original vertices.

For Boolean selected-vertex variables, the exact necessary condition is

\[
(x^{(0)}_{p_{a+1}}=0\ \land\ x^{(0)}_{p_{b-1}}=0)
\ \lor\
(x^{(1)}_{p_{c+1}}=0\ \land\ x^{(1)}_{p_{d-1}}=0).
\]

A boundary vertex absent from that block's prepared domain is already omitted. The condition does not require both blocks to omit both vertices. Its use as a cut inherits the native status of the width-43 exclusion; this review does not establish a Lean assembly of the finite cover or the resulting width-44 cut.

## Artifact hashes

| Artifact | SHA256 |
|---|---|
| `data/regions43.json` | `b1cf54d596bcd8e04162fef9741dca90eed03ab03e78089318614215d1b9b3da` |
| `data/first-edge-cover.json` | `da672a710470b035d04feec5ad23254ea4e663d72d34159ce3c7928d9ce0eacb` |
| `scripts/joint_first_edge.py` | `ea2c93b06696d829147ef64823d46246f24525fd6834e55a72d115eb5e192e02` |
| `data/first114-19.json` | `e332dcdd9857c21f39e7b1480fe91e6232b256dbddc0b4726e5f66ec54e7cdc3` |
| `data/first114-19-execution.json` | `7bb4688be406ac7d77a3d07969753eb2af381934eb9c97db4432cb956e7eab56` |
| `data/first114-19-114.pbtxt` | `f64503fa0c661429493c88de4b52f898c2b7a62cc11d68a934d45a209ee36d86` |
| `data/first114-49.json` | `568d59f76eb699860a489c32cc17999da832cd92924a7480e161ee2e4517d5ff` |
| `data/first114-49-execution.json` | `c0057730ed7fc818d7a28e96359f0ea179d72d8cae8e2883c9adab7abce902aa` |
| `data/first114-49-114.pbtxt` | `ee5804ad7da22b560046149959a70008babac57643696fe44e51cb21697f426a` |
| round-225 `data/pair43.json` | `d80e02584ec623c6bd2058d7e906f69a5fcfa1c7377d45c4eba25f9281dfc5b4` |
| `data/split43-zero.json` | `9cf937a1c0fa52927065ad53874c419d6f7813ad2afe988e9bd5ef281b09fc8c` |
| `data/split43-two.json` | `8fc54f0c42252f8638bbc29f688a3450d757b8e37c63e31ef1765dfa4902fb03` |
| `data/coverage43.json` | `440ea4f6766f0a4b8b7047e3fff8825e8ee25e1c248ecba97b4261a8bf00c74e` |

No worker, solver, compiler or software test was run by this review. Exact input arithmetic, saved-file comparison and source inspection were read-only. Earlier reviews, models, results and checkpoints were preserved; only this requested log was written.
