# Round 229: projection compatibility and crossing-count freedom

The fixed four-crossing construction is computationally excluded through two replacement blocks of at most 46 edges. All 315 maximal width-46 contexts are covered. A broader search removes the prescribed crossing count and excludes 304 contexts, leaving 11 unresolved. Its results also complete the six-crossing exclusion in this same family. No new snake or global upper bound has been obtained. The maintained interval remains \(191\le a(9)\le233\), with an independent rebuild of the contributor's completed upper-bound assembly still pending.

## Construction and exact projection restrictions

The source remains normalized bank 123, a 191-edge induced path from 0 to 88. The construction replaces two intervals by paths of the same lengths, preserves their original anchors and every outside index, and appends vertex 24. The proposed result has 193 vertices and 192 edges. The unwanted original neighbours of 24 occur at indices 7 and 143; index 191 is the intended attachment at 88.

The maximal width-46 intervals are \([a,a+46]\), \(0\le a\le6\), and \([c,c+46]\), \(98\le c\le142\). Their 315 pairs cover shorter permitted replacements by padding with unchanged original edges. Independent preparation review reconstructed all 630 part domains. Retained-vertex and endpoint restrictions, degree peeling, connectivity and colour capacity exclude 106 contexts and leave 209 pending. These initial restrictions do not depend on the prescribed crossing count.

Across the two coordinate faces, adjacency is equality of the lower projections. For a lower domain \(D\), own upper projections \(U\), actual joining ports \(P\), and other upper projections \(O\), the exact filter is

\[
D\setminus\bigl((U\setminus P)\cup O\bigr).
\]

Only actual crossing ports are exempt from one's own upper projections. A lower anchor without an adjoining upper arm has no exemption. All projections from the other replacement are forbidden. The revised native preparation uses this distinction, correcting the general mask limitation identified in round 228. Same-face inducedness, disjointness and nonadjacency, and compatibility with retained outside vertices remain separate conditions.

`ProjectionPorts229` supplies three accepted general results. The first equates membership in this filter with the corresponding cross-face adjacency restrictions; it does not infer that an arbitrary supplied port list contains genuine joining ports. The second uses two actual induced paths, domain membership and their prescribed endpoint equality to prove that the single-port filter is equivalent to the exact indexed compatibility required by `LayerJoining.join`. Injectivity forces every permitted coincidence to have the intended two indices. The third proves that a positive-length lower path's fixed starting anchor cannot occur among the upper projections when only its final joining vertex is exempt. Its positive-length premise is essential.

These results connect a geometric domain condition to an existing path constructor. They do not certify extraction of ports from JSON, preprocessing preservation or complete enumeration. The native review separately checked the corrected masks on every saved configuration. The zero-edge lower-segment case is retained in the general preparation, although none occurs in the saved configurations.

## General crossing allocation and the four-crossing cover

Let \(A,B\le2\) be the numbers of upper anchors of the two replacements, and let \(a,b\) be their actual crossing counts. Matching endpoint parity gives \(a\equiv A\pmod2\) and \(b\equiv B\pmod2\). If two upper anchors cannot be joined without leaving the upper face, then \(A=2\) implies \(a>0\), and likewise for the second path. These conditions imply \(a\ge A\) and \(b\ge B\): the cases are nonnegative, odd, or positive even counts. If the available total is \(a+b=A+B\), both inequalities are equalities.

`CrossingAllocation229` proves this implication in two accepted theorems. Actual-path endpoint parity, face-capacity exclusion of zero crossings and the correct total remain explicit geometric premises. The module proves no literal context census.

For the four-crossing family, these conditions support a single lower segment in each replacement in 185 contexts: 20 have allocation \((0,1)\), 13 have \((0,2)\), 100 have \((1,1)\), and 52 have \((1,2)\). The other 24 contexts, IDs 34–42, 79–87 and 124–129, retain other possible allocations and are handled by direct queries.

Complete finite upper enumeration gives 3,535 configurations. The boundary restriction requires at least one block to omit both old neighbours immediately beside its anchors. If both blocks retained such a neighbour, inducedness would permit trimming one unchanged edge from each, producing the same complete candidate in the excluded width-45 family. This restriction therefore depends on the completed native width-45 four-crossing cover.

Instantiating the two boundary choices before grouping gives 7,070 branches: 5,866 fixed-boundary contradictions, 272 first-part disconnections, 46 second-part disconnections and 886 survivors. The survivors form 538 exact groups and 496 undominated lower-pair representatives. Eighty-nine supported contexts have no surviving template; the other 96 are covered by these representatives. One representative transfers by literal endpoint/length agreement and domain containment to a previously excluded round-228 task. The remaining 495 receive new queries: 487 are initially infeasible and eight are subsequently excluded by longer retries. All 24 direct queries are also infeasible.

The complete four-crossing context partition is

\[
106+89+96+24=315.
\]

The preparation and transfer reviews establish the native model's intended scope. Individual infeasibility results remain native solver evidence, including the reused task. Domain containment transfers a particular lower-pair task; it does not transfer a whole smaller-width exclusion to a larger family. The saved `coverage46.json` establishes no six-crossing or arbitrary-crossing conclusion by itself.

## Removing the prescribed crossing count

The six-crossing model removes the four-crossing boundary restriction and its closure dependency. If \(f\) is the number of unchanged coordinate-8 edges, it replaces the stored budget \(4-f\) by \(6-f\). The appended edge from 88 to 24 is not a coordinate-8 crossing. All 209 pending contexts are queried: 200 terminate INFEASIBLE and nine UNKNOWN, with no cycle cuts and no witness.

The unrestricted model then removes the exact total entirely. Its per-part parity variable is bounded by the actual number of available vertical edges, so no saved four- or six-crossing budget remains as a cap. It retains necessary endpoint parity, same-face capacity, exact vertex and colour counts, induced degrees and separation between the two blocks. The initial 106 geometric exclusions remain valid. The completed `free46` batch returns 77 INFEASIBLE and 132 UNKNOWN results.

A subsequent model strengthens those 132 unknown contexts with completed count exclusions. It forbids total four using the complete same-width four-crossing cover, and forbids total six only where the same-context six-crossing query is terminal INFEASIBLE. In terms of replacement crossings, the excluded values are \(4-f\) and, where justified, \(6-f\). The nine six-crossing unknowns supply no six-count exclusion. No boundary condition or total cap is reintroduced.

These inequalities preserve every actual candidate under their explicit native premises, even if they remove disconnected-cycle selections from the degree relaxation. Other crossing counts remain permitted. The completed `counts46` batch returns 101 INFEASIBLE and 31 UNKNOWN results. Its queried IDs equal precisely the 132 unknown IDs from `free46`.

| Completed stage | Queried contexts | INFEASIBLE | UNKNOWN |
|---|---:|---:|---:|
| Exactly six crossings, `six46` | 209 | 200 | 9 |
| No prescribed total, `free46` | 209 | 77 | 132 |
| With justified count exclusions, `counts46` | 132 | 101 | 31 |
| Longer count-exclusion queries, `counts46-long` | 31 | 20 | 11 |

These four completed stages have accepted execution receipts, exit code zero and no external stop; their source pins and result links match. The longer batch queries exactly the 31 preceding unknown IDs, with eight seconds allowed per query. Their batch-completion labels do not turn UNKNOWN rows into exclusions. The completed unrestricted stages account for \(106+77+101+20=304\) excluded contexts. They do not establish that changing the crossing count produces a compatible pair.

## Final frontier and next construction reduction

The final `free-summary.json` records 106 static exclusions, 198 native exclusions and 11 open contexts. The open IDs are 34, 38, 39, 40, 79, 83, 84, 124, 126, 128 and 129. Every one belongs to the 24 contexts that lacked the four-crossing single-lower-segment allocation reduction.

All nine initially unknown six-crossing contexts, IDs 13, 14, 15, 18, 42, 58, 59, 60 and 87, are excluded by the longer unrestricted queries. Those nine never received a six-count exclusion: the strengthened worker uses only the original 200 terminal six-crossing results for that constraint. Thus the deduction is acyclic. An actual six-crossing candidate in any of those nine contexts would satisfy the broader model, including its justified exclusion of total four, contradicting its terminal native infeasibility. Together with the original 200 and the 106 static contexts, this excludes exactly six crossings throughout the 315-context family. The original nine UNKNOWN records remain unchanged.

The next proposed reduction targets exactly two total crossings. In IDs 34, 38, 39 and 40, the retained edges already contribute two crossings, so the replacement allocation must be \((0,0)\). Both replacements would be lower-face paths. In the other seven open contexts, the retained edges contribute one crossing; the first replacement has anchors in opposite faces and the second has both anchors below. Endpoint parity forces allocation \((1,0)\) when the total is two. Each resulting case has one lower segment in each replacement and is therefore suitable for a new exact lower-pair reduction with the established projection mask. The relevant lower-face capacities do not reject these allocations.

This is a proposed next-round reduction, with no enumeration or solver result claimed for it. Parity and capacity permit total two; they do not prove that any compatible candidate exists or that every candidate must have two crossings. The endpoints lie in the same face, so the total is even. Retained crossings rule out zero, while totals four and six are excluded by the completed native evidence; even totals of at least eight remain outside the proposed two-crossing reduction.

## Verification limits

`ProjectionPorts229` passed with three exported axiom reports and `CrossingAllocation229` with two. Their accepted sources and dependencies match the receipts. The reports use only the standard axioms `propext`, `Quot.sound` and, in the allocation theorem, `Classical.choice`. The checked results are general projection compatibility and allocation implications. Native extraction, finite upper enumeration, boundary mapping, coverage assembly and solver contradictions remain separate evidence. There is no end-to-end Lean certificate of the 315-context numerical exclusion.

The candidate audit is unchanged across the direct models: a reported witness must have 193 distinct vertices, adjacency exactly at consecutive indices for every vertex pair, retained anchors and outside positions, and endpoints 0 and 24. The unrestricted model records the actual coordinate-8 crossing count rather than imposing four or six. Cycle cuts exclude selections containing a whole cycle, a necessary condition for any induced path. The dormant inherited-exclusion branch is unreachable on the pinned input, which contains only pending and crossing-independent static rows.

This note uses the five source reviews `preparation-review.md`, `projection-proof.md`, `six-crossing-model-review.md`, `free-crossing-model-review.md` and `count-exclusion-model-review.md`, together with the completed receipts. No script, solver, compiler or software test was run for this note. All construction conclusions retain the fixed seed, appended endpoint 24, two length-preserving blocks and outside/anchor agreement. Other seeds, endpoints, block counts and length-changing constructions remain outside the search.

## Principal evidence hashes

- Four-crossing cover: `ee942f3ecc3bd7b1fbf665f5d345db10d0ef8153c62ea9c87dfff8189347d6a2`.
- `six46.json`: `264151fb16f02911a84eaedd98d86603c794536a94a0748136068c2600293256`.
- `free46.json`: `989bd19af02982e01a4c5c41246b5db907dc0c72c703518db3c0d7faeeb91460`.
- `counts46.json`: `51684ec7d346a965ae18b8a7f5dc0c4eb4d0d427d4aa5be5d66c749b9a175f6a`.
- `counts46-long.json`: `769f4a3ddd0e2369e7f46ba954caeaf9ff8288415efeb43a40f2f200da637264`.
- Accepted `counts46-long-execution.json`: `64bfd8f9aa9011c6528c007a6b7af013d8abd19bb0da66dc9c0dca0f81e1a448`.
- Final `free-summary.json`: `9b3273c9c0b091d05926effa0165553c7e974f78776fb69b4019de0bca9861bb`.
- Accepted `ProjectionPorts229.lean`: `e394b38fa880561845de63e83a602cb981d9ac5543d22148307894fa2c7c667e`.
- Accepted `CrossingAllocation229.lean`: `72fb63806cd05f817df52a4e5a94c694ab7b07feed2399378f34ef18ad833dd4`.
