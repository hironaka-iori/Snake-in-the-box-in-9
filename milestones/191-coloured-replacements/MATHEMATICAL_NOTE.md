# Round 191: attachment balance and compatible dimensional lifts

The user requested a pause after this round. Publish the completed work and pause. Resume only upon a new user instruction.

## Mathematical findings

Let P and Q be induced paths with the same endpoints. Write D for omitted vertices, A for added vertices, and C for common vertices. Every retained vertex v satisfies

|N(v) intersect A| = |N(v) intersect D|.

The path degree at v is unchanged, and the neighbours in C are identical. Subtracting the common neighbours proves the identity. Thus no added vertex may touch a retained vertex that lost no neighbour. This is a pointwise refinement of the previous total attachment balance. The one-vertex case is immediate.

In a bipartite graph, extending a path with fixed endpoints by 2k edges gains k vertices of each colour. Alternation gives equal colour counts for opposite-colour endpoints and a difference of one for same-colour endpoints. That difference remains unchanged. For 95 to 97 edges, the colour counts grow from (48,48) to (49,49).

Lean accepts two modules with seven dependency reports. AttachmentBalance191 checks the finite count partition, cancellation under equal-neighbour-degree premises, and cancellation for coloured subsets. AlternatingCounts191 checks alternating sequence counts, the 96-to-98 vertex consequence, and the singleton-component arithmetic. The generic path-to-finite-list correspondence remains written. Three failed source elaboration attempts are preserved; no failed attempt is presented as accepted. The resource limits were unchanged.

If r omitted vertices form c components and the gain is two, the r+2 added vertices also have c components. At least max(0,2c-r-2) added components must be singletons. Each singleton attaches to two retained vertices at Hamming distance two. Deletion leaves c+1 retained chains. Their c new connectors have total edge length r+2+c, so their endpoint distances, for any chosen chain order and orientation, cannot sum to more than this. These are necessary filters, with no sufficiency or performance claim.

## Common 95-edge component

The model selects 98 vertices of Q8 with the same endpoints as the saved common 95-edge path. It imposes exact induced degrees, 49 vertices of each colour, the exchange edge identity, and all 1792 square inequalities. No deleted-interval restriction is used. The initial model is a relaxation permitting longer disconnected cycles. A valid path is always a feasible point of this relaxation.

| Maximum omitted vertices | Outcome | Seconds |
| --- | --- | --- |
| 6 | INFEASIBLE | 13.203 |
| 7 | INFEASIBLE | 30.344 |
| 8 | UNKNOWN | 120.015 |

No dynamic cycle cuts were needed in the first two queries. Hence every fixed-port 97-edge replacement must omit at least eight original vertices and add at least ten, subject to the native solver evidence. There is no Lean contradiction certificate for these exclusions. This statement concerns this labelled path and its cube-isometric copies, not all 95-edge paths or a global Q9 upper bound.

The known 97-edge seed placement retains 52 of the original 96 vertices, omitting 44. The remaining minimum-omission range is therefore 8 through 44, with the lower end computationally qualified. The direct query that fixes the first Q9 surrounding context and allows all 162 permitted middle vertices remains UNKNOWN after 120.016 seconds. No 193-edge construction results.

## Lower dimensions and the useful change in search objective

For a middle path of b edges and two compatible outer paths using u vertices in total, the lift has b+u edges. The two outer components have u-2 edges, and the two crossings restore the difference. The objective must include compatibility, rather than the middle length alone.

With the displayed optimal 26-edge Q6 path fixed, the solver finds and bounds a 48-edge two-crossing lift. Its outer paths have lengths 2 and 18. An independent exhaustive enumeration finds 10,381 possible paths from each port in the allowed graph, including singletons. Across compatible pairs, the maximum is 22 outer vertices, again giving 48 edges. The enumeration makes 89,358,246 pair checks after pruning by size and completes in 12.938 seconds. The full path lists and witness are retained. This is complete native evidence; no complete Lean enumeration certificate is claimed.

The previously Lean-checked construction reaches 50 using a shorter 24-edge middle and outer lengths 18 and 6. Thus the specific comparison is

2 + 26 + 18 + 2 = 48 < 50 = 18 + 24 + 6 + 2.

This does not classify all optimal Q6 snakes. It shows that choosing this optimal middle loses against a compatible shorter middle.

For the displayed 50-edge Q7 middle, optimization finds an 89-edge Q8 lift in 120 seconds, without proving optimality. The earlier singleton-inclusive exclusion of all lifts of at least 98 edges applies to exactly this middle. Its restricted attainable maximum is therefore between 89 and 97, with native evidence for the upper endpoint. The new optimization's loose objective bound is not substituted for that earlier exclusion.

For the displayed 98-edge Q8 middle, the 192-edge Q9 target remains unresolved after 180 seconds. All three models allow singleton outer paths. Every selected component must contain a port by flow conservation; ports have degree at most one, all selected degrees are at most two, and the edge count is vertex count minus two. Consequently there are precisely two path components, one at each port. Returned witnesses are checked by all pairs of vertices.

## Frontier and next work

No new Q9 record, unconditional upper bound, or optimality proof for 196 was obtained. The most useful new observation is the concrete failure of middle-length maximization in Q6 to Q7. On resumption, vary the middle and outer paths jointly, including crossing vertices. Do not restrict every attempt to near replacements of the common 95-edge path. A two-crossing target of 192 or 193 is already valuable; neither requires claiming the final maximum is 196.

The eight-omission query remains an optional local subproblem. If pursued, use the attachment and component structure to change the search, rather than repeating the unchanged 120-second model. Larger cycle exclusions or a component-connector enumeration are possible refinements. The new identities are already consequences of full induced-degree constraints, so merely adding them again is not a demonstrated improvement.

Keep native solver optimality, complete native enumeration, Lean arithmetic/counting, and the generic graph interpretation distinct. All 84 saved common-middle surrounding contexts have ample vertices of each colour; colour capacity alone does not settle their compatibility.

The inherited upper-bound project is unchanged: archived 235 awaits a complete independent rebuild; 233 and 234 retain local and graph premises. Round187 has 93/98 clause batches and 11,904/12,424 clauses checked; the critical contradiction and actual-snake transfer remain pending. The direct Q8 all-pairs Lean recheck from round188 is also pending. The manuscript-wide consistency review was completed in round190; the next scheduled review is round200.

No contributor commits appeared during the initial refresh. The contributor branch remains f393c48e5e583e57d3cbb66e4330f960033229b1. The unrelated .gitignore and milestone50 critical-family edits are preserved. The manuscript author order and local hyperlink settings remain unchanged.
