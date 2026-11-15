# Round 223: joint four-crossing construction

The goal is active. This round pursues constructions only. No snake longer than 191 edges was found. The useful completed result is a checked five-component constructor, together with a checked endpoint exclusion argument and a new joint search that permits both faces and all four crossing locations to change.

The working hypothesis is that coordinated changes in both Q8 faces can produce a 192-edge snake. Existence is unproved. The number 196 remains a further target, without a recurrence or optimality argument.

## Lower-dimensional evidence and joining theorem

The saved Q7 and Q8 snakes decompose as

\[
18+24+6+2=50,\qquad 8+25+10+25+26+4=98.
\]

The final summands count crossings. The Q7 example uses a compatible 24-edge middle component, rather than a longest 26-edge component. The Q8 example contains two 25-edge paths in one Q7 face, using 52 vertices; a single longest Q7 path has 51 vertices. These examples motivate optimizing compatible components together. They are particular witness decompositions, not a classification of all optimal snakes or a universal dimensional recurrence.

Let P0 through P4 be oriented induced paths in Qn. Consecutive paths must have exactly one common projected vertex, at their prescribed joining endpoints. Every nonconsecutive same-face pair must be disjoint and nonadjacent. The two nonconsecutive opposite-face pairs must be projection-disjoint; their projected vertices may be adjacent. Put the five paths in alternating faces 0,1,0,1,0. Their concatenation is induced and has length equal to the sum of the five component lengths plus four.

The reason is that same-face contacts are precisely base-graph adjacencies, whereas opposite-face contacts occur precisely at equal projections. The hypotheses eliminate every unintended contact and provide the four joining edges. Singleton outer components remain permitted. FourCrossings223 constructs the actual indexed path by four applications of the accepted append operation. Its Lean check passed in 5.141 seconds with only the standard reported axioms. It introduces no new graph or compatibility definitions. It proves an assembly implication, not existence of large compatible components or a concrete 193-vertex witness.

## Selected seed and joint model

The seed is bank entry 123, forest index 0 in the round 195 profile. Normalize its original coordinate 7 to bit 8. The five components have edge lengths 46,83,32,13,13; the lower face contains 94 vertices and the upper 98. Endpoints are 0 and 88, and the ports are 35,195,208,232. The two upper-face components have unequal lengths 83 and 13, so no symmetry exchanging those components is imposed.

The joint model selects 193 of all 512 Q9 vertices, with endpoint 0 retained and exactly four bit-8 edges. All crossing locations, both face occupancies and the second endpoint are variable. It requires at least one seed omission in each face and bounds their total by a specified budget. These restrictions define a search neighbourhood; they are not universal conditions on 192-edge snakes. Both-face omissions do not require any original port to change.

At every selected vertex v, selected cube-neighbour count equals 2 minus its endpoint flag. Endpoint flags imply selection and sum to 2. A vertical-edge flag equals the conjunction of its two vertex flags. Four crossings return the path to its starting face; even length from 0 requires an even endpoint. Thus the second endpoint is in the even lower face and the selected parity counts are 97 even and 96 odd. Keeping both old endpoints would make the target impossible by parity.

All 4608 coordinate squares forbid selection of all four corners. A degree-feasible selection can contain one path and additional cycles. An observed cycle is excluded by requiring one of its vertices to be absent. The script accepts a witness only after tracing a single connected path and verifying all unordered adjacency pairs. None of this round's runs produced a degree-feasible solution, so no dynamic cycle cut was needed.

## Computational outcomes

| Maximum omitted seed vertices | Added vertices if exactly that many are omitted | Native outcome | Solver-loop seconds |
|---:|---:|---|---:|
|4|5|INFEASIBLE|3.204|
|8|9|UNKNOWN|120.063|
|12|13|UNKNOWN|150.031|

If d seed vertices are omitted, exactly d+1 new vertices are required: the seed has 192 vertices and the target 193. The first run therefore gives a computational restriction of at least 5 omissions and 6 additions for successful changes in this seed alignment with endpoint 0, four bit-8 crossings and at least one omission in each face. It has no Lean contradiction certificate. The other two runs reached their limits and establish no exclusion. The model's mathematical interpretation received an independent source review.

All three native receipts completed normally within the resource limits. An earlier startup attempt had only 977,797,120 free bytes and launched no solver; the subsequent accepted runs passed the 1 GiB startup threshold. Native source, initial serialized models and execution receipts are retained. The initial model plus any recorded cycle cuts would be required for replay; all current cut lists are empty.

## Endpoint-directed consequence

In an actual indexed induced path, any selected neighbour of the last endpoint occupies its unique preceding index. Therefore retaining one neighbour excludes every distinct neighbour from the path. Endpoint223 checks this argument and its exclusion consequence for an irreflexive undirected relation; both results passed in 2.140 seconds.

Retain old endpoint 88 internally and choose 80 as the new endpoint. Since 80 XOR 88 = 8 and 80 XOR 208 = 128, both 88 and 208 are adjacent to 80. Vertex 208 must therefore be omitted. It is an old crossing port, so this choice forces a crossing change. With at most 12 omissions and the other joint restrictions unchanged, the corresponding query is UNKNOWN after 75 seconds. No new path or exclusion follows.

The eight lower-face neighbours of 88 are recorded in data/endpoint-cases.json with their seed neighbours. One is the already selected predecessor 89; the other seven are eligible new endpoints for the specialized search. The table marks this distinction explicitly. The eligible cases cover immediate extension at 88 only; arbitrary endpoint relocation remains broader. The specialized model retains a base scope phrase about a free endpoint, followed by its explicit specialization. Its command and equality fix endpoint 80 unambiguously; data/endpoint-scope.json states the exact restricted scope.

## Verification and next calculation

Two Lean modules supply three checked public results. Their accepted sources, objects and dependency receipts are retained. Concrete numerical model infeasibility is native only. The constructor's generic premises have not been instantiated with a new 192-edge snake. No software tests were created or run.

The next useful calculation should use explicit endpoint choices and mandatory omissions to reduce the reconnection problem, rather than repeat an unchanged broad timeout. Endpoint 24 requires removal of two separated seed vertices 28 and 56, at indices 7 and 143. After fixing those omissions, retained intervals can be treated as path components whose contacts with replacement vertices must satisfy the same joining principle. Any further restricted search must retain its exact coverage and parity conditions. The balanced four-crossing seed remains an alternative; no new symmetry should be imposed on the unequal 83/13 pair.

The maintained interval remains 191 to 233. The contributor branch advanced to e4d8f6a31d5485b95b0c211117102038e680ad1c. Its notes describe a candidate 231 calculation and a generic/toy Lean chain, with generated tables, shards, covers, certificates and glue still pending. This branch was inspected without merging or independent rebuilding. No completed 231 result is asserted here. The existing 233 independent full rebuild remains pending and outside this constructive round.

The round 222 fixed-parent exclusion and frozen parent-history searches remain unchanged. The manuscript and frontier explanation are updated in place, preserving authors and hyperlink settings. The next complete manuscript review remains round 230.

The final publication fetch advanced the contributor revision to 4b6b73907af9d76d7a8f3ca592a13dc89c8ad21d. The intervening commits are labelled work in progress and add a 232 plan scan, splitting draft, certificate records and generation scripts. They do not change the maintained interval in this round. The opening observation and final revision are recorded separately.
