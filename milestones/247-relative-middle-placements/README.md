# Round 247. Disjoint middle paths in a nine-dimensional crossing construction

**Result.** The 47-edge middle shared by five known 96-edge snakes in \(Q_8\) has exactly one disjoint congruent copy in \(Q_7\). Allowing all relative placements therefore leaves the maximum at 191 in the two-middle construction of Round 246. If the second middle may change shape, its longest possible length is 48. Exactly five labelled paths attain it. None of those five permits a join of 192 or more edges, even with all four outer pieces, both endpoints and the crossing site free.

## Which eight-dimensional snakes were compared?

The displayed optimal 98-edge snake and all five 96-edge examples have blocked endpoints. Their least-used coordinates give different cuts. The 98-edge representative crosses every coordinate at least four times. Each 96-edge arm crosses one coordinate twice and has the same 47-edge middle between those two crossings, up to symmetry. The three 96-edge segments obtained by trimming the displayed optimal snake all have an extendible endpoint. For a join across one coordinate, the 98-edge representative can accept at most a 92-edge partner. Each of the five 96-edge shapes accepts a 94-edge partner. Thus testing how two projected paths fit together gives information that their individual lengths do not supply. [Representative data and prior proofs](../246-eight-dimensional-parents/README.md) · [Exhaustive optimum in eight dimensions](https://research.aalto.fi/en/publications/exhaustive-search-for-snake-in-the-box-codes/) · [Published nine-dimensional examples](https://arxiv.org/abs/2607.15270) · [Reference lengths and paths](https://minortriad.com/snake/)

## The disjoint congruent copy

Write a vertex of \(Q_9\) as \((u,y,x)\), with \(u\in Q_7\). The construction crosses \(x\) once in \(y=0\), and crosses \(y\) twice on each side of \(x\). Fix the labelled upper middle \(P\) in the first arm. A vertex shared by the two upper projections would give an additional \(x\)-edge. For an axis permutation \(\pi\), a translation \(t\) gives a disjoint copy exactly when \(t\) is absent from the set of differences \(u\oplus\pi(v)\) for \(u,v\in P\).

Of the 5,040 axis permutations, 5,039 give every possible difference. Only the permutation exchanging axes \(0,3\) and \(2,4\) misses a difference, namely 22 (binary \(0010110\), least significant bit numbered zero). The resulting cube map is a parity-reversing involution. Its 64 vertex pairs include 48 with exactly one vertex of \(P\) and 16 with neither. Counting set intersections separately across all 645,120 isometries gave the same unique map and the same labelled path as the recorded mate. The exact 191 result for that placement therefore applies to every relative placement of two congruent copies. [Direct intersections](orbit.json) · [Differences for every permutation](independent-check.json) · [Prior 191 witness and 378 checked certificates](../246-eight-dimensional-parents/proof-replay.json)

## Allowing a different middle

There are 80 vertices outside \(P\). A 48-edge path uses 25 vertices of one parity and 24 of the other, with both endpoints in the majority. Select the indicated numbers, require two endpoints of degree one, and require degree two at every other selected vertex. Each disconnected solution contains an induced cycle and its cycle vertices cannot all belong to a path. Block the cycle. On obtaining a connected path, block its 49-vertex set. At fixed cardinality this removes exactly that path up to reversal.

The search found two 48-edge paths with even endpoints and three with odd endpoints. Neither parity admitted another solution. A balanced 49-edge query was infeasible, ruling out all longer paths by truncation. Separate 50-edge queries also closed in both parities. The five paths share between 36 and 42 vertices with the old 48-vertex mate. At least six of its vertices must change even for the closest longest partner. [Path sequences and exhaustion records](complementary.json) · [Certificate replay](cert-replay.json)

An independent enumeration grew induced paths from each of the 40 even starting vertices. Each 47-edge path has one even endpoint, so it occurs once. Extending both ends of these paths recovers every 48-edge path from its two endpoint trims. Keeping only the extension that introduces the smaller endpoint counts each once. The search pruned by available parity counts, the reachable component, and disjoint four-vertex stars (a path must omit a vertex of each). It exhausted all 40 starts in 302,371,435 search nodes and compared every pair of vertices in each emitted path. It recovered all five 48-edge paths and all 100 examples from the capped 47-edge Boolean search. [Complete native enumeration](q7-census.json) · [All ordered paths](q7-census-paths.txt)

| Partner length | Labelled paths, up to reversal | Distance between endpoints |
|---|---:|---|
| 47 | 1,108 | 691 at distance 3 and 417 at distance 5 |
| 48 | 5 | 2 at distance 4 and 3 at distance 6 |

## Lifting the five longest partners

The middle interiors exclude \(46+47=93\) sites for the unique crossing, leaving 35 sites per partner. For each crossing \(q\), both \(Q_8\) arms start there in their own face. An arm of length \(a\) contains \(\lfloor(a+1)/2\rfloor\) vertices of each parity, with one additional vertex of the starting parity when \(a\) is even. A fixed middle vertex has the opposite parity in the arm to its \(Q_7\) label, since it is in \(y=1\). Subtract the actual middle counts and the forced lower vertices from the parity totals. For a 48-edge middle its two upper parity counts differ by one.

At each site the calculation allowed every ordered pair of arm lengths \(a,b\le98\) with \(a+b+1\ge192\), covering lengths 192 through 197. Every one of the 175 sites was excluded. The independent checker regenerated the formulas, checked the path and cycle blocking clauses, and verified all five middle-enumeration refutations and all 175 lift refutations. The formulas were regenerated using the recorded encoders. The known 191-edge path satisfied the updated formula with both of its 47-edge middles, and all 18,336 unordered vertex pairs were checked. A separate attempt to reattach the new middles to the outer pieces of 20 archived examples found no join of at least 188 with the specified short reattachments. [Lift formulas and outcomes](lifts.json) · [Proof files](lift-proofs/) · [Independent replay](cert-replay.json) · [Known-path control and reattachment limits](positive-control.json)

A positive example with one middle of each length uses crossing site 22 and two 89-edge arms. Their join has 179 edges. All 16,110 unordered pairs of its 180 vertices passed direct inspection, and the pinned vertex set satisfied every clause of the parity model. Thus the maximum over the five mixed families is between 179 and 191 inclusive. [Ordered witness and checks](mixed-witness.json)

## Changing one vertex of the congruent mate

Among the 1,108 disjoint 47-edge paths, four remove one vertex of the original mate and add one new vertex. In the saved labelling the four (removed, inserted) pairs are (118, 124), (76, 88), (76, 104) and (107, 122). There are no two-vertex replacements and exactly four three-vertex replacements. For each one-vertex replacement we allowed every one of the 36 eligible sites and every arm-length pair capable of reaching 192. All 144 refutations passed independent replay. Together with the earlier exact 191 ceiling for the congruent mate, this leaves 1,103 labelled 47-edge partners to consider in this construction. Any improving one must delete at least three of the mate's 48 vertices. [Exchange histogram and site queries](near-lifts.json) · [Proof replay](near-replay.json)

## One 96-edge parent with an unrestricted partner

With a complete 96-edge \(Q_8\) arm fixed, translate either endpoint to zero. The opposite arm begins there, avoids the other 96 projected parent vertices, and may use any crossing pattern in its own eight-dimensional face. A 95-edge partner has 48 vertices of each parity. If a longer partner existed, its first 95 edges would also qualify. The search imposed these counts, induced degrees and local face bounds. A square can contribute at most three selected vertices. A three-dimensional face can contribute at most five. Omitting two antipodes leaves a six-cycle; omitting two other vertices leaves a selected vertex with all three neighbours. Either is incompatible with an induced path.

Four of the ten endpoint queries were certified directly. The six unresolved root queries were divided over their seven possible first steps. Of 42 resulting cases, 26 were certified and 16 reached their individual time limit. One more entire endpoint closed. Class labels and endpoint order follow the stored parent paths.

| 96-edge class | Endpoint 0, remaining first steps | Endpoint 1, remaining first steps |
|---|---|---|
| 0 | 1, 2, 32, 64 | Excluded |
| 3 | 2 | 16 |
| 4 | 32, 64, 128 | Excluded |
| 5 | 1, 2, 8, 16, 32, 64, 128 | Excluded |
| 8 | Excluded | Excluded |

For class 8, an explicit 94-edge partner attains the upper bound. Its maximum single-crossing join is exactly \(96+1+94=191\), with no restriction on the opposite arm. Each table entry that lists a number remains open in that direction. [Ten root queries](partners.json) · [Root proof replay](partners-lrat.json) · [First-step outcomes](partner-children-summary.json) · [First-step proof replay](partner-children-lrat.json)

## Research direction and scope

The parity, symmetry and lower-dimensional construction proposals in the working note motivated this round. A reroute between the same endpoints in a bipartite cube has the same length parity as the original segment. A positive gain at fixed endpoints is therefore at least two. The one-edge gain examined here instead changes an entire middle and frees both endpoints of the joined path. The separate search involving four replacements in one parity class remains open.

The isometry counts and the 47-edge census are native enumerations. The projection and truncation arguments are written deductions. Lean checked the two colour counts and endpoint colour of an abstract alternating arm, including the exact quota before subtracting fixed vertices. The cube-to-model correspondence is a written argument. The Boolean exclusions have independently replayed proof certificates. The full-cube project interval is \(191\le a(9)\le231\). The upper endpoint comes from the contributor's saved proof audit at revision 478869ee; an independent full dependency rebuild is pending. [Lean statements](ArmParity247.lean) · [Compiler receipt](ArmParity247-compile.json) · [Contributor theorem and audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/tree/478869ee1ec6ff3a10ddb6ba7a2a1d89fbb82088)

**Pause checkpoint.** The nearest remaining 47-edge partners are the four three-vertex replacements. Shorter middles and the five archived 191-edge constructions with a different crossing pattern also remain possible. The next full written-source review is due at Round 250.
