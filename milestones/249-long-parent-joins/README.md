# Round 249. Long parents and movable crossings

**A single-crossing snake of 192 edges requires a long eight-dimensional parent outside the fifteen shapes in the original inventory.** These are eleven 96-edge, three 97-edge and one 98-edge shape. Exactly the five 96-edge parents classified in Round 248 attain 191. Each of the other ten parents gives at most 190. Donors 99 and 114 both attain 190. Seven further long shapes have been constructed for the next round. [Independent coverage audit](audit.json) · [Original parent sequences](../248-rooted-arm-capacity/parents.json) · [New sequences and hashes](geometry.json)

## From the six remaining 96-edge parents to the whole inventory

Translate the joining endpoint of the parent to zero. The partner can use every vertex of the opposite eight-dimensional face except the other projected parent vertices. The only cross-face edge then joins the two copies of zero. For a 96-edge parent, targets of 95 and 94 partner edges give 192 and 191 joined edges respectively.

| Partner length | Complete root exclusions | How the remaining root closed | Checked contradiction certificates |
|---|---:|---|---:|
| 95 | 11 of 12 | At the last endpoint of donor 15, each of the seven first steps was excluded. | 18 |
| 94 | 11 of 12 | At the first endpoint of donor 16, five first steps were excluded directly. The remaining two had five admissible second steps in total, all excluded. | 21 |

Each query fixes the parity counts and requires the induced degrees of a path, including both endpoints. Disconnected selections may contain cycles. Every cycle cut is valid for an induced path and its vertex set is recorded. The solver returned proof traces for the excluded cases. A separate checker replayed those traces. The audit reconstructed the formulas, verified the proof-file hashes, checked the geometric prefix coverage, and independently verified the positive paths against every vertex pair. At length 93 the two explicit witnesses for donors 99 and 114 reach 190. The complete length-by-endpoint evidence also records the open shorter cases. [Length 95](partners-95.json) · [Length 94](partners-94.json) · [Length 93](partners-93.json) · [Length 92](partners-92.json) · [Constructive witnesses](witnesses.json) · [Audit method](audit.py)

Each 97-edge parent begins at either end with a rooted copy of a checked 96-edge subpath. In the stored labelling the pairs of subpaths used at the two ends are as follows.

| 97-edge donor | First endpoint | Last endpoint |
|---|---|---|
| 18 | 15, first | 16, last |
| 19 | 16, first | 17, last |
| 902 | 901, first | 17, last |

Any partner avoiding the longer parent also avoids its rooted subpath. At each of the six indicated roots, the shorter parent excludes even a 93-edge partner, so all three 97-edge shapes give at most 190. For the 98-edge parent, its first 96 edges from root 0 are donor 15 rooted at its first endpoint. From root 78 they are donor 17 rooted at its last endpoint. Both 96-edge subpaths exclude a 92-edge partner, improving the earlier 191-edge ceiling to 190. Since a join of at least 192 admits a partner prefix giving exactly 192 while the long parent is kept intact, these statements cover every longer join with any of the fifteen parents. [Root-preserving coordinate maps and bounds](audit.json) · [98-edge exclusion](../222-prefix-certificates/MATHEMATICAL_NOTE.md) · [Five other 96-edge parents](../248-rooted-arm-capacity/README.md)

## How much can the saved 98-edge parent attain?

For each of its two endpoints, direct searches exclude partner lengths 91, 90 and 89. Longer partners contain those shorter prefixes. At both endpoints there is an explicit 80-edge partner, verified together with its full nine-dimensional lift. Thus the largest single-crossing join from this 98-edge parent lies **between 179 and 187 edges inclusive**. Even its upper bound is four edges below the 191 attained by five of the 96-edge parents. Seven first-step cases at root 0 and three at root 78 remain open at partner length 88. This uncertainty does not affect the classification at 191 or 192. [Independent audit of both endpoints](audit98.json) · [Ordered paths and direct proofs](direct98.json) · [Constructive searches](positive98.json)

## Moving the crossing along a fixed projected path

Let $w_0,\ldots,w_m$ be distinct vertices in one cube with consecutive vertices adjacent. Duplicate $w_k$ across the two faces of the next cube, placing $w_0,\ldots,w_k$ on one side and $w_k,\ldots,w_m$ on the other. This lift is induced exactly when every nonconsecutive adjacent pair $w_i,w_j$, with $i<j$, satisfies $i<k<j$. The two copies of $w_k$ give the only cross-face coincidence. A chord in either arm survives exactly when the cut fails its strict inequalities. The valid crossing positions therefore form an integer interval, possibly empty. Lean checked both the equivalence for the indexed path and the interval property. [Lean source](Hinge249.lean) · [Compiler and axiom reports](Hinge249-compile.json)

In the 191-edge bank, 25 paths have a single-crossing projection, and all 25 projections have exactly one permissible crossing position. In the 190-edge bank there are 373 such projections, of which 372 have one position. Seed 4 on coordinate 8 has two, at indices 94 and 95. Direct prefix and suffix checks recovered the same intervals. All accepted lifts were checked as nine-dimensional paths.

Extending either end of a 190-edge projection by one unused neighbour, then allowing the crossing anywhere, gives 50 labelled extensions from 45 projections. Up to cube isometry and reversal, they are exactly the 25 single-crossing 191-edge classes already in the collection. Applying that operation to the 25 longer projections gives no 192-edge lift. [Exhaustive cut and endpoint-extension records](crossings.json) · [Published construction and archive source](https://arxiv.org/abs/2607.15270)

## New parents on the same construction route

The predecessor and successor of an interior vertex of a cube path have exactly two common neighbours. One is the current vertex. Replacing it by the other gives the only possible change at that one position. The resulting path must still be induced. Checking all 1,430 initial positions, then repeating on every new shape until no further shape appears, gives exactly 22 shapes up to cube isometry and path reversal. The seven additions comprise five 96-edge and two 97-edge shapes. The recorded 98-edge path has no legal interior change of this kind. Larger changes and replacing endpoints can give other shapes. [Full list of moves and ordered new paths](geometry.json)

**Next case for Round 250.** In donor 16, replace vertex 82 by 16 at position 72, between vertices 18 and 80. The endpoints are 1 and 70. Any 95-edge partner must visit 82 within its first 94 edges, since otherwise its 94-edge prefix also fits the original donor. The parity of 82 agrees with the parity of either joining endpoint, so it must be internal in a 95-edge partner. Its two incident edges must use two of the six neighbours remaining available there. Both joining endpoints remain open. The full manuscript review is due in Round 250. [Active route and subsequent cases](../../further-research/routes/ACTIVE.md) · [Reusable research goal](../../further-research/routes/RESEARCH_GOAL.md)

## Global scope

The reviewed interval is $191\le a(9)\le231$. The saved contributor audit for 231 is preserved at revision e0ddaefc. The 230 assembly still assumes certificate families. An independent rebuild of the complete 231 dependency chain remains pending. This round resolves a finite construction family and gives a crossing criterion for arbitrary simple projected words. The maximum length of a nine-dimensional snake is open. [Contributor audit for 231](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/36-lean435-port/audit231/final-audit.txt) · [Conditional assembly for 230](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/37-230-feasibility/ASSEMBLY.md)
