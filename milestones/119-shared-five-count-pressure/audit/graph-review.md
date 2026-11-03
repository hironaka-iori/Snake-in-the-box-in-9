# Independent review of the oriented thirteen-rule graph experiment

The bounded saved-cycle audit passes. The graph has1601856 states and4697823 retained edges. The two added rules remove no further edges beyond milestone117. Both replacement cycles receive zero bonus from all thirteen rules, and the computed profile means, ranges and comparisons are unchanged:

| Profile | Cycle length | Mean | Potential range | Comparison | Integer part |
| --- | ---: | --- | --- | --- | ---: |
| Completed | 18 | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Conditional floor18 | 3 | $496$ | $602$ | $551765/2348$ | 234 |

These remain conditional numerical graph results. There is no new negative Lean theorem, completed actual-snake upper bound, or improved comparison.

## Orientation and shared credit

`scripts/evaluate_oriented.py` normalizes the six-transition word up to coordinate relabelling and reversal. If reversal is required, it reverses the five count symbols before applying the asymmetric bounds. Both new rules are stated in the canonical orientation of $012304$:

- Completed-b: bounds $[(2,2),(6,21),(2,2),(3,3),(6,21)]$, assumed total at least23.
- Conditional-a: bounds $[(2,2),(6,21),(4,4),(2,2),(6,21)]$, assumed total at least23.

The applicability test requires the whole interval represented by each symbol to satisfy its bound. Symbol6 represents $[6,21]$, and is never treated as exact6 for this test. Both rules necessarily include symbol6 in the summed positions. Therefore neither can remove an entire bucket through an exact-count contradiction. Applicable clipped totals are always19 and20, giving suffix credits96 and72 with coefficient24. The reported449 and446 positive-credit keys describe the separate rule tests; these numbers should not be presented as disjoint counts or counts of actual weight increases after taking the maximum.

Both placements are inspected for deletion; only placement1 earns edge credit. Credits from competing rules are combined by a maximum under the shared weighted-excess budget. The selected positions and coefficients are reversal-symmetric, so reversing the count order preserves their meaning. The new direction shape has different canonical words in its two orientations, avoiding a tie for these asymmetric guards.

The independent script tests2180 reversal cases over the saved direction table and the two new rules. For each saved cycle edge it reconstructs normalized counts before testing every bound, deficit, deletion and credit. It agrees with the producer. The producer also asserts exact reproduction of the milestone117 removal set and both complete weight-vector hashes after its first eleven rules. This review inspected those assertions and their pinned inputs; it did not rerun either full weight vector.

## Saved certificate checks

The audit checks full direction/history/count keys against the original graph arrays, accepted paths through the retained diagram, original endpoint and weight reconstruction, count-free floors, all thirteen rules at both placements, retained-edge membership and cycle chaining. It hashes the saved potential bytes, checks the state count, minimum zero and stated range, and verifies equality in the potential inequality at every cycle edge. Exact rational cycle means and comparison arithmetic agree with the result record. No full-edge inequality scan was repeated; the numerical lower certificates over all graph edges rely on the pinned producer's checks. The algorithm-source identity was taken from the independently pinned milestone117 audit, without a fresh Git retrieval.

All rule deficits vanish on both replacement cycles, including at placement0. Consequently, these cycles give coefficient-independent ceilings for this fixed thirteen-rule family with nonnegative coefficients. The balanced coefficient24 calculation attains those ceilings according to the producer's all-edge inequalities. Further coefficient changes alone cannot raise the mean above these saved cycle values. This assertion concerns the fixed graph rules and does not rule out additional geometric or global constraints.

## Replacement windows and one next test

There is no common canonical five-centre direction shape between the two replacement cycles. The completed cycle uses $012034$, $012301$, $012304$ and $012310$. Its changed $012304$ tuple is $(2,5,2,4,6)$ and its $012301$ tuple is $(4,2,5,2,4)$; the new exact $012304$ guards therefore miss it.

The conditional cycle uses only $012031$ and $012314$. Its three full keys are:

| Original edge | Direction index | History | Nine directions | Six count symbols |
| ---: | ---: | ---: | --- | --- |
| 18806 | 2 | 0 | $012031043$ | $(6,3,3,6,3,3)$ |
| 1130461 | 108 | 0 | $012302432$ | $(3,3,6,3,3,6)$ |
| 2139520 | 198 | 0 | $012314210$ | $(3,6,3,3,6,3)$ |

The exact normalized five-count windows are $012031$ with $(3,3,6,3,3)$ or $(6,3,3,6,3)$, and $012314$ with $(6,3,3,6,3)$. The audit JSON records every placement and reversal.

The most useful single bounded next test is the full nine-transition context of edge18806. Use direction word $012031043$ and eight internal-centre bounds

$$[(0,21),(0,21),(6,21),(3,3),(3,3),(6,21),(3,3),(3,3)].$$

The first two centres are unrestricted; centres3 through8 carry the graph's six symbols. Testing this in the full cube without an additional total cap targets the entire interval bucket and includes the extra directional context missing from a five-centre test. A negative result would need its own certificate and semantic bridge. A positive result would need independent path verification. Imposing total at most24 on those six counts would force the two large counts to equal6 and would only test that narrower case; it could not justify deletion of the complete bucket. No such new test was run in this review.

## Proof-status boundary

The two new negative rules have saved native replay records, not Lean refutation theorems. The completed-b record reports5480 input clauses,19264 deductions and2240349 hints; conditional-a reports6250 input clauses,43795 deductions and5045692 hints. This review read and pinned their metadata without repeating those replays.

The subsequently saved `data/negative-audit.json` reports a separate plain-encoding rebuild and positive-hint RUP replay for both cases, with byte-identical full CNFs,6311 variables, and104436/104438 clauses. Its case hashes and deduction counts agree with the certificate metadata above. This graph review inspected that record without repeating the encoding rebuild or proof replay. The negative Lean semantics, contradiction proofs and actual-snake transfer remain pending.

Separately, `Counterexample119.lean` is successfully checked: it constructs the actual `Snake 148` with window start43 and exact counts $(3,6,3,4,6)$, disproving the broader proposed total lower bound23 even under the low-four restrictions. The source, object, log, snapshots and151 dependency hashes were verified. Its nine axiom reports use only `propext` and `Quot.sound`, with runtime36.656 seconds. This positive theorem does not contradict the two narrower new negative hypotheses.

## Pins

- `data/full-critical23/results.json`: `83523df8acd4b8506e0407608ded961dbca6be02e8cf6195e28d72f0cda724f3`.
- `scripts/evaluate_oriented.py`: `1e0ebf7878e411e6451e01d4c041930fb51bacf35585431ae9f73d5f68bd1a9b`.
- `scripts/independent_graph.py`: `c08684b805fffc4f39d1bbfff71b6fdec1a30e5b93981943b260a7ca74e3e2e1`.
- `data/graph-audit.json`: `76a3119d3410330827418c5039203e579ccd27a91c7c9315d786eb78c9bcb177`.
- `data/Counterexample119-audit.json`: `0864e98a8a3d05e0d77851b8e7e2cab87636dd976f625d0ee51004d8b862f90d`.
- Completed-b native certificate metadata: `f00409af1ec7743b65cb3589f8d0a3a8d0e35fe38dede6e7cb44d67c7370cb3a`.
- Conditional-a native certificate metadata: `e09f985529c105836a9ecd2f5e868900fc4cd543c7c4fab76819bfeab4ae91a2`.
- `data/negative-audit.json`: `e7143624de56ae704eb2f12f2a2544c58c6e0a3a12845866fae9af1389fd5c98`.

No substantive orientation or saved-cycle inconsistency was found. Only the owned audit script, JSON and report were written. No solver, compiler, full graph computation or Git command was run.
