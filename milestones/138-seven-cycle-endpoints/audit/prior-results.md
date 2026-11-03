# Existing results relevant to the seven-edge cycle

This is a bounded reading and direction-pattern audit. No solver or Lean
process was run for this note. The comparison does not establish a new
exclusion or endpoint theorem.

## Authoritative occurrence and its shorter window

The source is
`milestones/131-odd-pair-six-count/data/odd-pair9-six25/conditional_floor18-profile.json`.
Its seven-edge cycle has mean 496. Row 992157 has directions

\[
012301430
\]

and six recorded count symbols

\[
(6,3,3,3,5,2).
\]

The six symbols refer to vertices at offsets 3 through 8 from the beginning
of the nine-direction word. Symbol 6 means a count in [6,21], not equality
to six. The alignment is also explicit in the five-count slices of
`milestones/131-odd-pair-six-count/scripts/evaluate_graph.py`.

Take the six transitions at offsets 3 through 8. They are
`[3,0,1,4,3,0]`, which relabel to `012301`. Their five internal counts are
exactly

\[
(3,3,3,5,2).
\]

The corresponding normalized vertices are
`[0,1,3,7,15,14,12]`. This shorter window keeps all three consecutive threes
and the nearby two, while removing the clipped count completely. Row 1273862
contains the same six-direction/count window at direction offset 2.

## What the checked results do and do not imply

1. **The earlier endpoint demand requires eight directions `01234031`.**
   Under that direction hypothesis, a pair sum at offsets 2 and 6 of at most
   seven forces an endpoint at Hamming distance two from the first centre.
   The source is `milestones/45-pair-endpoint-demand/lean/EndpointDistance.lean`,
   theorem `endpoint_at_distance_two`; its completed receipt is
   `milestones/45-pair-endpoint-demand/data/verification.json`.
   Neither orientation of this eight-direction word occurs in any of the
   seven saved nine-direction rows. The direction hypothesis therefore fails.

2. **The newer endpoint and occurrence results require `012032`.**
   The pair-at-most-nine conclusion and its common-neighbour strengthening
   apply to that particular shape. Neither orientation of `012032` occurs
   in any of the seven saved rows. Consequently the checked twenty-four-window
   theorem from milestone 137 does not count this cycle's windows.
   Sources: `milestones/132-odd-pair-endpoint/lean/ActualEndpoint132.lean`,
   `milestones/134-endpoint-geometry/lean/CommonNeighbor134.lean`, and
   `milestones/137-actual-block-assembly/lean/ActualCount137.lean`.

3. **The distance-three pair bounds have different seven-direction words.**
   The paper's Proposition `prop:distance-three-pair` requires `0123410`
   or `0123415` and bounds counts at offsets 1 and 6 by ten or nine.
   Neither word, in either orientation, appears in the seven saved rows.
   No endpoint conclusion is stated in that proposition in any event.

4. **A checked inequality does match the shorter window, but is satisfied.**
   For `012301`, the completed result is

   \[
   \alpha_{r+1}+\alpha_{r+5}\ge5.
   \]

   The candidate gives 3+2=5. Source:
   `milestones/48-low-count-compatibility/lean/SumWindow481.lean`,
   theorem `low_count_sum`, with its completed
   `data/verification.json` receipt. This result has no endpoint conclusion.

5. **The complete small-pair catalogue also admits the relevant pair caps.**
   Its only maximal forbidden cap combination for `012301` is
   offsets (1,5) with caps (2,2). The candidate has (3,2), so that exclusion
   does not apply. The actual survey file
   `milestones/49-six-direction-pair-catalogue/data/s3-p15-c32.json`
   records a SAT local assignment with caps (3,21,21,21,2).
   The catalogue's completed proof status is recorded in its README and
   `data/verification.json`. This local witness says nothing about the
   three extra exact counts (3,3,5), and is not a complete snake.

6. **The sharp triple sum does not concern three consecutive counts.**
   The milestone 50 theorem requires `012340` and proves

   \[
   \alpha_{r+1}+\alpha_{r+4}+\alpha_{r+5}\ge13.
   \]

   See `milestones/50-three-count-return/lean/TripleDemand.lean`, theorem
   `snake_demand`, and `data/verification.json` for its checked dependencies.
   That six-direction word is absent in both orientations from all seven
   saved rows. The consecutive triple (3,3,3) lies in a four-direction
   `0123` segment; substituting it into the unrelated triple-sum theorem
   would change both the positions and the direction hypothesis.

7. **Other superficially similar restrictions also miss the candidate.**
   The checked asymmetric pair exclusion of caps (3,2) requires `012342`,
   rather than `012301`; see
   `milestones/48-low-count-compatibility/lean/LowCountCompatibility.lean`.
   The outer-four-at-most-three exclusion requires `012031`, and the
   middle-count-two/outer-sum-nineteen theorem requires `012314`.
   Neither shape occurs in the saved nine-direction rows in either
   orientation. The generic no-three-twos result does not apply to
   (3,3,3). The checked five-centre share-48 row has directions `012314`
   and counts (3,3,3,A,5), with A at least six, so it also does not match
   this shorter word and its counts.

The pattern comparisons above were made on every contiguous subword of the
seven authoritative direction rows, with coordinate labels canonicalized
in both orientations. They concern the specific listed results, not an
exhaustive search through every theorem in the repository.

## One selected candidate and the new discovery status

The selected candidate is the single six-direction window `012301` with
exact internal counts (3,3,3,5,2). If an endpoint-free test is subsequently
needed, a precise initial conjecture is that an endpoint lies in the union
of the Hamming balls of radius two around its three count-three centres
1,3,7. Its counterexample query would forbid endpoint indicators in that
union while retaining the same window and counts. This is a proposed
endpoint-demand set only; none of the checked results above proves it.

The root investigation has already obtained a stronger numerical lead:
`work/base/run-status.json` and `work/base/worker-status.json` report
`UNSAT_UNCERTIFIED` for the full nine-direction row `012301430`, with
internal count ranges

\[
([0,21],[0,21],[6,21],3,3,3,5,2),
\]

without endpoint restrictions and without added cycle cuts. There was one
solver call and no model; the worker records 0.297 seconds and 100891 clauses.
The final input SHA256 is
`6d2d511598a767640b37575873faf0af98c390c939289939f156bfc3f7e6d7c3`.

Accordingly, the selected next action is to test and certify the shorter
`012301`/(3,3,3,5,2) exclusion with no endpoint restrictions. The provisional
endpoint-demand query is unnecessary if this ordinary exclusion succeeds.
The current full-row UNSAT result remains uncertified. It does not yet
exclude an actual snake, remove a proved graph edge, or improve a global
bound. A shorter certificate would need its actual count interpretation
and arbitrary-coordinate transfer, followed by a new graph computation to
assess the effect of removing the saved cycle.
