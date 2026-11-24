# Round 265 · Changing both arms of a one-crossing snake

A 191-edge snake from the published one-crossing examples cannot reach 192 by regrowing both tails while keeping its central 77 edges and the same single crossing. There are 25 such examples. In a separate search, one 96-edge parent from the Round 253 catalogue now has a verified 182-edge join, up from 132 at that endpoint. [Results](summary.json) · [182-edge path in vertex order](best-open-join.json)

## Which changes can the known 191-edge paths accommodate?

The two eight-dimensional faces of a chosen coordinate are copies of the same cube. Project the crossing endpoints to zero. The two arms form an induced path if both are induced in their faces and the only vertex they share after projection is zero. Their edge lengths and the crossing edge add.

Exactly 25 of the 131 archived 191-edge shapes cross some coordinate once. In all 25, the two arm lengths are 96 and 94. Keeping the crossing edge and the first 38 edges outwards on each side fixes a 77-edge central segment. Up to a common permutation of the eight coordinates and interchange of the faces, there are nine such segments. For a representative of each, the enumeration below counts labelled completions once in a fixed orientation.

| Edges retained on each side | Central edges | Representatives completely enumerated down to length 190 | Completions of length 190 | Completions of length 191 |
|---:|---:|---:|---:|---:|
| 40 | 81 | 9 of 9 | 56 | 25 |
| 38 | 77 | 9 of 9 | 56 | 25 |
| 36 | 73 | 6 of 9 | At least 44 across all nine | At least 19 across all nine |

At width 38 all 81 completions give distinct nine-cube shapes up to coordinate permutation, translation and reversal. The two source archives contain all of them. The exact maximum with any of these central segments is 191. Three shorter-segment searches reached their work limits. [Full enumerations with both tails](conditional-190.json) · [Separate run starting at 191](conditional-191.json) · [Independent tail-mask enumeration](tail-pairs.json)

**Why the enumeration covers both tails.** A completion of length at least 190 must have first-arm length between 91 and 98. For every extension of the first prefix in that interval, enumerate extensions of the second prefix avoiding the entire chosen first arm except at zero. A new site must be unused and touch precisely the current tip among its own arm's occupied sites. This rule preserves inducedness and includes the next step of every possible continuation. An alternating suffix must fit in the available connected component of its tip, with enough vertices of each parity. A degree-one vertex in that component distinct from the tip can occur only at the free end. These necessary conditions allow early termination of branches. Length 192 would also be detected before any longer result could be accepted. A separate program enumerates the two tails independently and intersects their occupancy masks. It excludes length 192 for six of the nine 77-edge segments and all nine 101-edge segments. [Conditional traversal](ConditionalPairs.cs) · [Independent mask traversal](TailPairs.cs)

## Which simultaneous changes can leave the published collection?

The source archives contain 1,042 distinct shapes of length 190 and 131 of length 191. Selecting a coordinate used once gives 373 rooted arm pairs at length 190 and 25 at length 191, up to symmetry. In each arm make any equal-length replacement of at most one occupied site, preserving an induced path rooted at the crossing. One may then extend the free tip by one edge, keep it, or delete it. Apply the choices in both faces together, and keep any compatible pair with total length at least 190. Only the resulting pair of arms must be mutually compatible.

**All 398 starting pairs form a closed set under this operation.** Of the 4,423 ordered transitions, 398 retain the same pair, 4,025 go to a different pair and 2,230 change both arms. Every result is already in the source collection. Hence a route from any of the 398 examples to length 192 with these moves and the same crossing must visit a join of length at most 189.

For a direct enumeration, deleting an interior site leaves two components. The new site must attach to the end of the component containing the root in a way that leaves the root an endpoint. It can then meet either end of the other component. The second choice reverses the suffix. Deleting a free tip leaves one component. In every case we enumerate available attachments, require the exact neighbour set in the retained sites, and allow each terminal edit. An independent calculation instead deletes the site, tries insertions next to the remaining component ends, reconstructs the induced path from zero, and checks root degree and connectivity. The two enumerations recover the same ordered transitions. [Exchange enumeration](exchange.py) · [All 398 pairs in physical coordinates](exchange-states.json.gz) · [Source entries and crossing axes](exchange.json) · [Independent graph reconstruction and archive comparison](audit.py)

## Construction at other crossing endpoints

Round 253 listed 348 endpoints of 174 long-arm shapes. Applying the saved length and exclusion filters left 284 endpoints of 96-edge arms in the present screen. We placed 14,519 distinct directed donor words from 130 donor shapes under every permutation of the eight coordinates, retaining the previous construction whenever it was longer. Two resulting joins reached 173 and twelve reached 172. The 14 leading endpoints and a 191-edge control supplied the starts for regrowth. The regrowth also allowed a blocking site on the opposite arm to be vacated by replacing an interval there.

At endpoint zero of the arm identified by `7745b3cd`, the Round 253 construction had length 132. Placement alone gave 172. Keeping the 96-edge arm fixed and regrowing the opposite arm to 85 gave $96+1+85=182$. An independent check examined all 16,653 unordered pairs of vertices. Regrowth with both arms changed also attained 182 from this construction. The changed 191-edge control was archive entry 6. These are attained lengths. The 37 bounded regrowth runs do not determine the maximum for the 284 endpoints. [Placements and input hashes](placements.json) · [Regrowth records and explicit partners](growth.json) · [Direct search](JoinedSearch.cs)

## Sources and reproduction

The 191-edge source is the [project's archived bank](../../work/bank9.json). Place the authors' [pinned record archive](https://github.com/Math-AI-Caltech/Snake-in-the-Box/blob/46c765399353a588ea50444a5d6610f53102b1c2/record_snakes.csv.zip) at `work/record_snakes.csv.zip` to repeat the comparison against the 1,042 paths of length 190. The calculation checks the member hash against the [Round 244 source record](../244-190-path-construction/results.json). [Authors' paper](https://arxiv.org/abs/2607.15270)

The [run receipts](runs/) give the program, arguments, source hash and resource measurements for each calculation. Use the [guarded runner](../256-two-exchange-parents/run.py) to execute the milestone scripts. In order, the stages are `rank.py`, `growth.py`, `tails.py`, `conditional.py`, `exchange.py` and `audit.py`. The JSON files preserve the completion status for each bounded search. The [manuscript comparison](manuscripts.json) records the source mirrors and compiled PDFs.

The global interval remains $191\leq a(9)\leq230$. The contributor branch still points to the revision with the saved upper-bound audit. An independent full rebuild remains pending. [Verified 191-edge witness](../../outputs/snake9_witness.json) · [Pinned contributor theorem and audit](../264-distant-component/contributor.json) · [Active route](../../further-research/routes/ACTIVE.md)
