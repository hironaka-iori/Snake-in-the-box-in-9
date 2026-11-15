# Round 230: face visits and the completed two-block exclusion

The selected construction family is now computationally excluded for every number of crossings, through two replacement blocks of 46 edges. This is progress on understanding a restricted construction. It produces neither a longer snake nor a global upper bound. The research goal pauses after this round at the user's request.

## Family and hypothesis

Use normalized bank123, a 191-edge snake with endpoints 0 and 88. Append vertex 24 after 88. Its two conflicting retained vertices are 28 at index 7 and 56 at index 143. Replace two separated intervals by paths of the same respective lengths, preserving each anchor and every outside position. At width 46 the maximal intervals are [a,a+46], a=0,...,6, and [b,b+46], b=98,...,142: 315 contexts. Padding a shorter replacement with unchanged seed vertices embeds it in a containing maximal context.

The round began with the hypothesis that two total crossings of coordinate 8 might yield a construction in one of the eleven contexts still unresolved after round 229. The other 304 contexts were already excluded for every crossing count. Four and six crossings were excluded throughout the family. This hypothesis has now been excluded computationally within the specified family.

## Two crossings

The eleven residual context IDs are 34,38,39,40,79,83,84,124,126,128,129. Their retained parts have respectively two crossings in the first four contexts and one in the other seven. The appended edge changes coordinate 6. Endpoint parity and the prepared face capacities force replacement crossing allocations (0,0) and (1,0), respectively.

Enumerating the short upper pieces gives fifteen compatible template descriptions, each leaving two induced paths in Q8 to find. The lower domains exclude unintended equal projections of upper vertices; only actual joining endpoints receive exemptions. All fifteen complete native queries returned INFEASIBLE. They used no boundary-change condition from the older four-crossing search. The coverage is recorded in data/coverage-two46.json.

A separate source and finite-data review reproduced every upper template and domain. It also found three pairs of equivalent descriptions, 0/4, 1/5 and 2/6, by peeling the forced first edge 0 to 1. This is exact identity of the assembled full path. The equivalences were observed after the submitted fifteen-task batch and were not needed for its coverage.

## A necessary inequality for visits to a coordinate face

Let a nontrivial induced path cross a selected coordinate c times. Let u and l count its vertices in the two faces, and let r be its number of endpoints in the upper face. Then

\[
3c\leq2u+r,\qquad 3c\leq2l+2-r.
\]

For c=0 both statements follow from nonnegativity. Suppose c>0. Split the path into maximal consecutive visits to the two faces. A visit with a crossing on either side cannot contain only one vertex: its two flanking vertices would coincide. It cannot contain only two vertices: its flanking vertices would be adjacent at nonconsecutive positions. Every internal visit therefore has at least three vertices; each endpoint visit has at least one.

If there are k upper visits, exactly r of them meet an endpoint. Counting crossings incident with upper visits gives c=2k-r. Counting vertices gives u>=3(k-r)+r=3k-2r. Eliminating k gives 3c<=2u+r. The lower-face argument is identical with 2-r endpoints. For a path of m edges, addition yields 3c<=m+2. Thus a replacement of 46 edges has at most 16 crossings in a selected coordinate. No dimension-specific assumption is used in this argument.

Lean accepted three components in FaceVisits230: the interior-visit obstruction for actual compatible induced pieces; a finite-list vertex budget; and its conversion to the face inequality under explicit incidence and endpoint-count premises. The extraction of maximal visits and those premises from a whole path is the written argument above, still outside the Lean code. The accepted source has three standard-axiom reports. Two earlier failed elaboration attempts are preserved separately; they are not accepted proof records.

## Closing the remaining contexts

Every full candidate has its endpoints in the same face, so its total crossing count is even. Each of the eleven residual contexts retains at least one crossing, so zero is impossible. The completed same-context exclusions for two, four and six therefore require at least eight crossings.

The final model imposes this minimum and the two face inequalities on each replacement, while permitting every remaining crossing count and retaining the original geometric conditions. The candidate path remains an induced path in each replacement, so the inequalities are necessary even though the native degree relaxation may additionally permit disconnected cycles. No boundary-change restriction is imposed.

All eleven queries returned INFEASIBLE on their first solve; no cycle cuts were needed. Together with the prior 106 geometric and 198 native exclusions, this covers all 315 contexts. The preceding six-crossing dependencies are acyclic: its nine initial unknowns were excluded by unrestricted queries that did not impose a six-count cut on those nine. The exact-two calculation uses the prior cover, and the final visit calculation uses the completed exact-two result.

The literal unrestricted cover is data/coverage-free46.json. Raw native models remain locally available and are archived in data/solver-models.zip. Solver contradictions, finite enumeration, extraction and cover assembly remain native evidence. No claim of an end-to-end Lean certificate is made.

## Frontier at the pause

The maintained interval remains 191<=a(9)<=233, with an independent full rebuild of the contributor's 233 assembly pending. The first constructive target remains 192 edges; 196 is a conjecture. The fixed-parent one-crossing ceiling from round 222 and the frozen coordinate-history frontiers remain unchanged.

Resuming this construction route requires changing at least one family restriction. The most useful next preparation is to compare endpoint extensions and their blocker locations across the saved 191-edge seeds, grouping literal cube-isometry duplicates before choosing a new seed or endpoint. A candidate with fewer or more closely placed blockers may require less retained structure to change. Such an improvement is a hypothesis and no new seed survey was performed this round. Wider or length-changing replacements are alternatives. Partial greedy growth remains available for a later suitable subproblem.

The full manuscript and short explanation received a complete source review this round. Historical open statuses are dated, the abstract and reading guide are shortened, and the current construction result is added with its verification limits. No new work continues after publication and the requested pause.
