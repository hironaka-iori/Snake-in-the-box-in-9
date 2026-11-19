# Round 246. Comparing eight-dimensional parents and their nine-dimensional joins

**Exact result for a construction in \(Q_9\).** Fix the relative positions of the two 47-edge middles described below, let both ends of each middle cross to the other face, and permit a single crossing between the two eight-dimensional arms. The maximum is **191 edges**, even when all four outer pieces, both global endpoints and the joining point are free. There is an explicit 191-edge witness and a separately replayed refutation for each of the 378 crossing and arm-length cases that could exceed it. This theorem concerns that construction family. [Complete finite calculation](ceiling.json) · [Independent proof replay](proof-replay.json)

Twenty of the 25 recorded 191-edge snakes that cross a coordinate just once have the same pair of 47-edge paths in \(Q_7\), in the same relative positions up to a single cube isometry. All five 96-edge arm types used by the 25 snakes have blocked endpoints. Each nevertheless has a compatible 94-edge arm that produces 191 edges in \(Q_9\). The saved optimal 98-edge representative admits a one-crossing join of **at most** 191 edges. The eight-dimensional maximum is 98. This comparison uses a specified 98-edge representative and all the 96-edge arms in this 25-example family. [Eight-dimensional optimum](https://research.aalto.fi/en/publications/exhaustive-search-for-snake-in-the-box-codes/) · [Nine-dimensional source paper](https://arxiv.org/abs/2607.15270) · [Pinned public paths](https://github.com/Math-AI-Caltech/Snake-in-the-Box/tree/46c765399353a588ea50444a5d6610f53102b1c2) · [Ceiling for the 98-edge representative](../222-prefix-certificates/MATHEMATICAL_NOTE.md)

## Length, endpoint extension and coordinate cuts

| Eight-dimensional path | Endpoints that can grow | Endpoint Hamming distance | Fewest crossings of a coordinate | Piece lengths after that cut |
|---|---:|---:|---:|---|
| Displayed optimal 98-edge path | 0 | 4 | 4 | \(8,25,10,25,26\) |
| Five 96-edge arm types in the recorded joins | 0 in all five | 2 in four types, 4 in one | 2 in all five | \(31,47,16\) or \(25,47,22\) |
| Three 96-edge windows obtained by trimming the 98-edge path | 1, 2, 1 | 2, 4, 4 | 4 in all three | Each regrows to the original 98-edge path |

Piece lengths count edges within faces. Add the edges that cross the cut to recover the original length. The representative 96-edge arm and the 98-edge path have respective sorted coordinate counts \((2,3,4,13,16,18,18,22)\) and \((4,5,7,8,13,14,21,26)\). A blocked path cannot occur consecutively in any longer induced path because that longer path would provide a legal end extension. This proves the distinction from a truncation without any uniqueness assumption for the eight-dimensional optimum. [All representative paths and endpoint counts](comparison.json) · [Independent cut and pair verification](arm-structure.json)

There is a strict comparison relevant to lifting. Each of the five 96-edge classes admits a compatible partner with at least 94 edges. The displayed 98-edge class admits partners of at most 92 edges when only one crossing is allowed. Thus the shorter classes admit strictly longer partners. Attainment of 92 for the displayed optimum is open.

Cutting the 25 published examples at their single crossing gives five classes of length 96 and five of length 94. Every class pair occurs exactly once. The class labels are the first zero-based record IDs. The entries are the bank IDs of the joins.

| 96 class / 94 class | 0 | 1 | 2 | 7 | 20 |
|---|---:|---:|---:|---:|---:|
| 0 | 0 | 1 | 2 | 7 | 20 |
| 3 | 12 | 14 | 3 | 19 | 23 |
| 4 | 15 | 13 | 4 | 18 | 24 |
| 5 | 5 | 6 | 10 | 16 | 21 |
| 8 | 8 | 9 | 11 | 17 | 22 |

The 47-edge middle cut from every 96 class is the same up to symmetry. It also occurs in 94 classes 0, 1, 2 and 7. The 95-edge middle arm found in 84 other nine-dimensional examples contains this same path in its decomposition \(31+47+15+2=95\). [Earlier dimension cuts](../188-dimensional-constructions/MATHEMATICAL_NOTE.md) · [Whole-path comparisons](arm_structure.py)

## A construction with two fixed seven-dimensional paths

Write cube vertices as \((u,y,x)\), with \(u\in Q_7\). The join crosses \(x\) once. In 20 bank examples both arms cross \(y\) twice. In the two \(y=1\) faces, the 47-edge paths are disjoint in projection to \(Q_7\). The 20 examples produce five labelled middle pairs. For each, the saved coordinate permutation, translation and order choices map **both** paths to one reference pair. The reference pair itself is exchanged by swapping coordinates \(0,3\) and \(2,4\), then applying XOR with 22. A second application undoes the first. Coordinate 1 changes at every vertex, so the exchange has no fixed point. [Paths, joint maps and reference involution](middle.json)

Four outer pieces lie in \(y=0\). For each \(x\), the two pieces must be disjoint and mutually nonadjacent. Each meets its own middle exactly at its prescribed crossing port. Between the two \(x\)-faces, the outer sets must meet exactly at one point, an endpoint on each side. These conditions suffice by direct enumeration of the possible cube adjacencies. If the four outer edge lengths sum to \(s\), the joined length is \(2\cdot47+4+1+s=99+s\). Thus the known joins have \(s=92\), and a 192-edge construction requires \(s=93\).

Aligning seven-dimensional pieces from the donor collection supplied 39 rooted outer paths at one port and 48 at the other. Including every legal single terminal addition gave 66 and 90. Recombination on the common middle yielded 198 labelled arms of lengths 92 through 96. Their compatible joins reached 191 on each of the five labelled placements. The search covered the specified pieces and terminal additions. [Construction and verification](middle.py) · [Results](middle.json)

## Searching complete placements of longer arms

From the 1,042 recorded 190-edge paths and 131 recorded 191-edge paths, take every contiguous 93- through 98-edge window lying on one side of a coordinate cut. Include windows of the displayed optimal \(Q_8\) path and every endpoint extension of the resulting arms through length 98. Up to cube isometry and reversal the collection contains 364, 375, 149, 11, 3 and 1 paths of lengths 93 through 98 respectively. This is an explicit collection of 903 shapes. [Extraction and input hash](donors.py) · [Paths and provenance](donors.json)

Two paths in opposite faces produce a snake by one crossing exactly when their projections meet only at the designated endpoints. Translating both endpoints to zero leaves \(8!\) possible relative coordinate permutations. Including both endpoint choices on each arm gives \(161\,280\) labelled placements per ordered length pair. The length splits below exhaust the possibilities for a one-crossing 192-edge snake because each \(Q_8\) arm has length at most 98.

| Target arm lengths | Shape pairs in the collection | Fewest unwanted projected coincidences |
|---|---:|---:|
| 98 and 93 | 364 | 9 |
| 97 and 94 | 1,125 | 6 |
| 96 and 95 | 1,639 | 1 |

All \(504\,483\,840\) target placements were evaluated. All 25 known 96-and-94 joins were also reconstructed. Exactly five target shape pairs attain one extra coincidence, each at a unique labelled placement. All five use the same 95-edge arm, formed by extending 94 class 7. Its new tip coincides with the long arm at distance 83, 89, 89, 95 or 95 from the joining root. Each lifted walk has 193 distinct vertices and precisely one chord. That chord closes an induced cycle of length 180, 186, 186, 192 or 192. The last two cycles coincide up to isometry and circular order with the published 192-vertex coil from Round 243. The absolute coordinate maps and all-pairs checks are saved. [Placement minima and witnesses](placements.json) · [Native computation](Place.cs) · [Independent replay](placements.py) · [Cycle identifications](coils.json)

Keeping this 95-edge partner fixed, an independent search regrew the corresponding 96-edge arm from its joining endpoint. For every one of the five placements, retaining the first 48 edges precludes a 96-edge completion; for two placements retaining the first 40 already precludes it. At shorter prefixes several searches reached their 500,000-node limit. Those cases remain unresolved. [Regrowth record](regrow.json)

## Free assignment of the two arms on a fixed projection

Each original 96-and-94 pair has a projected union of 191 vertices and joining root zero. A target projected union of 192 vertices must contain 96 vertices of each parity, so growing the old union by one vertex requires an odd addition. A third occupied neighbour of the root cannot be assigned to either arm without violating its endpoint degree. This excludes six of the 33 unused odd vertices. The 25 examples yield \(25\cdot27=675\) descriptions of 660 distinct projected sets.

Delete the root from each candidate projected set and take its induced graph \(G\). Let \(a_v\) indicate adjacency to the root. An arm sign \(c_v\in\{-1,1\}\) gives induced degree \((\deg_G(v)+c_v(A_Gc)_v)/2+a_v\). The two outer endpoints have opposite colours and opposite projected parities. Choose the even endpoint \(p\) to have sign \(+1\) and the odd endpoint \(q\) sign \(-1\). Degree two at the other vertices requires
\[
 (A_G+\operatorname{diag}(\deg_G(v)+2a_v-4))c=-2(e_p-e_q).
\]
The two nonzero residues modulo three encode the signs uniquely. Exact elimination gave nullity 0, 1 or 2 in 423, 217 and 20 distinct sets respectively. The search enumerated all eligible endpoint pairs and all surviving sign assignments. All 660 sets were excluded. This permits the other 190 nonroot original vertices to change face assignments or traversal order while retaining the joining point and projected union. [Method](repartition.py) · [Per-union outcomes](repartition.json)

## Exact ceiling with all four outer pieces free

The two prescribed middles have 46 interior vertices each, and their projections to \(Q_7\) are disjoint. The common crossing vertex may be any of the other 36 vertices, including a middle endpoint. The involution exchanging the middles pairs the crossing sites into 18 orbits. Exchanging the faces also exchanges the lengths \(a,b\), so the calculation retains both orderings. Each arm lies in \(Q_8\); consequently \(a,b\le98\). Any improvement requires \(a+b\ge191\). There are 21 ordered possibilities per representative site and 378 cases in total. This covers lengths 192 through 197 without assuming that shortening a path preserves the fixed middles.

Exactly \(a-47\) lower vertices belong to the first arm, since its upper middle contains 48 vertices. The upper middle has 24 vertices of each parity; if the outer count is odd its surplus has the parity of the crossing vertex in \(Q_7\). Apply the same rule with \(b\) for the second arm. The encoding selects each lower copy of a middle endpoint and both copies of the joining point. Extra crossings between the two arms are forbidden. Each arm has one outer endpoint of the parity dictated by its length. The degree in the full selected graph must equal one at these endpoints and two elsewhere. Any selected cycle is forbidden in an induced path. These restrictions hold for every possible set and ordering of the four outer pieces.

An initial length-192 run excluded 11 of the 18 site orbits. Dividing the remaining seven by their six ordered length splits excluded all 42 cases. The final enumeration rebuilt the model with separate face and parity counts for each pair of lengths, allowed either parity of the total length, and excluded all 378 cases. The archived known 191-edge path satisfies its model and passed a separate check of all 18,336 vertex pairs. For each excluded case, the independent replay regenerated the Boolean formula, matched its SHA-256 digest, and replayed its proof to the empty clause. The 378 proof files are included. [Initial site search](free-outer.json) · [Length-192 refinement](outer-refinement.json) · [Final enumeration](ceiling.py) · [Proofs](ceiling-proofs/) · [Independent checker](VerifyLrat.cs) · [Replay receipts](proof-replay.json)

The shape comparisons are native finite evidence. The joining and degree identities and the reduction to the 378 cases are written arguments. The individual Boolean exclusions have independently replayed LRAT certificates. There is no new Lean theorem in this round. The reviewed global interval is \(191\le a(9)\le231\), with an independent full rebuild of the contributor's 231 theorem pending.

**Pause checkpoint.** The next construction decision is to vary the relative placement of the two 47-edge middles, or replace one middle. Rearranging only the four outer paths cannot reach 192 in the recorded placement with this crossing pattern. The five bank examples whose 94-edge partner uses at least three crossings offer a separate observed pattern. Full written-source review is next due at Round 250.
