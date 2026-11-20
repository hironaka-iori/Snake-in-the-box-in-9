# Round 250 · Single-crossing joins retaining 84 consecutive edges

**The maximum in the following construction family is 191 edges.** Take a snake in the nine-dimensional cube that crosses between two eight-dimensional faces once. Keep any 84 consecutive edges of any of the 22 reference paths inside an arm of at least 96 edges. Allow both ends of that arm to change freely and allow any compatible path on the other side. Exactly 25 long-arm shapes occur. Five attain 191 and the other twenty give at most 190. [Original fifteen parents](../249-long-parent-joins/README.md) · [Complete 84-edge census](cores-84.json) · [Independent census](core-audit-84.json)

## How the 98-edge and 96-edge examples compare

The saved 98-edge parent and the five successful 96-edge parents are induced paths in the same cube. Each has endpoints of the same parity, since each has even length. In the documented face cuts, the 98-edge parent has five pieces of lengths 8, 25, 10, 25 and 26, joined by four crossings. Each of the five 96-edge parents has a cut with two crossings and a common 47-edge middle, up to cube symmetry. Its outer pieces have lengths 31 and 16, or 25 and 22. These profiles belong to the specified examples. [Face comparisons and path records](../246-eight-dimensional-parents/README.md)

In nine dimensions, the two projected arms must share only their joining endpoint. The saved 98-edge parent admits a partner of at least 80 and at most 88 edges at each endpoint, giving a joined maximum between 179 and 187. Each of the five successful 96-edge parents admits a 94-edge partner and yields 191 edges. Thus starting with two extra edges in the first arm can leave substantially less room for the other arm. [Verified partner ranges](../249-long-parent-joins/audit98.json) · [Five 191-edge constructions](../248-rooted-arm-capacity/README.md)

## Changing one interior vertex

Suppose an old parent and a changed parent have the same joining endpoint and the sole vertex freed by the change is $h$. If $u$ bounds the old partner length at that endpoint, every partner of more than $u$ edges for the changed parent must reach $h$ by edge $u+1$. Otherwise its first $u+1$ edges would already be compatible with the old parent. If the full partner continues beyond that prefix, the visit is internal. Lean checks these two implications with the old numerical cap as an explicit premise. [Lean source](FreedSite250.lean) · [Compiler and axiom receipt](FreedSite250-compile.json)

In donor 16, the change at position 72 replaces 82 by 16 between 18 and 80. At the joining endpoints 1 and 70 the old partner caps are 92 and 91. A visit to 82 has even index from either root. Hamming distance gives the following necessary positions in a proposed 95-edge partner.

| Joining endpoint | Possible visit indices before the search | Result |
|---:|---|---|
| 1 | $4,6,\ldots,92$ | 95-edge and 94-edge partners excluded |
| 70 | $2,4,\ldots,92$ | 95-edge and 94-edge partners excluded |

Position zero denotes the joining endpoint. The solver used the necessary visit and, where forced by the old cap, two selected neighbours of the freed vertex. Ordered position restrictions were unnecessary. Both ends of all seven parents obtained by interior changes now exclude joins of 191 and 192 edges. Each calculation covered the entire rooted domain, including every choice of the far endpoint. The previous numerical caps are taken from the pinned Round 249 audit. [Changed paths](../249-long-parent-joins/geometry.json) · [Inherited bounds](../249-long-parent-joins/audit.json) · [191-edge replay](replay-191.json) · [192-edge replay](replay-192.json)

## Keeping one segment and regrowing both ends

A legal extension adds an unused neighbour of the chosen end that touches no other vertex of the path. Every induced completion containing a fixed segment can be constructed by first adding all missing vertices at the left and then those at the right. Each partial path is a consecutive part of the final induced path. One representative of each segment suffices because cube isometries and path reversal preserve the legal extensions. The ordered edge-coordinate sequence, standardized by first occurrence in both orientations, identifies these isometry classes exactly.

| Length kept | Occurrences in the 22 reference paths | Distinct segment shapes | Long parent shapes obtained | Additions to the 22 |
|---:|---:|---:|---:|---:|
| 88 edges | 205 | 96 | 23 | 1 |
| 84 edges | 293 | 134 | 25 | 3 |

An independent enumeration grew either end at each step and merged equivalent paths at each new length. It recovered every archived class in both rows. At 84 edges the final counts are nineteen 96-edge, five 97-edge and one 98-edge shapes. The three additions all have 96 edges. The table below uses the labelled representatives of the 84-edge calculation. The start index and both joining endpoints refer to those representatives. [Direct enumeration](cores.py) · [Independent algorithm](core_audit.py) · [84-edge audit](core-audit-84.json) · [88-edge audit](core-audit-88.json)

| New shape (hash prefix) | Source of retained segment | Start index in source | Edges added on left and right | Joining endpoints |
|---|---|---:|---|---|
| cd1a7e31 | donor 69 | 1 | 9 and 3 | 30 and 129 |
| 648fa151 | changed donor 16, position 72 | 0 | 0 and 12 | 1 and 134 |
| 4d2130c3 | changed donor 16, position 72 | 1 | 1 and 11 | 131 and 134 |

For each new shape, both roots exclude partners of 94 and 95 edges. These six rooted domains per target imposed only compatibility with the full parent. The opposite arm could use any induced path beginning at the chosen crossing. The 191 and 192 exclusions for the seven corner changes and the three regrown shapes used forty distinct LRAT certificates in total. Their formulas were regenerated, and every certificate was replayed against its formula. All forty closed at the root, without a prefix subdivision or cycle refinement. [New-parent 191 replay](extended-audit-191.json) · [New-parent 192 replay](extended-audit-192.json) · [Search ledgers at 191](extended-191.json) · [Search ledgers at 192](extended-192.json) · [Compressed proofs](proofs/)

## Scope and continuation

Any join of more than 192 edges with a specified long arm can be shortened to 192 by removing edges from the far end of its partner. Consequently every arm of at least 96 edges in a 192-edge single-crossing snake must avoid all 134 of the 84-edge segment shapes. The calculation leaves shorter common segments, long arms outside this family, and different crossing patterns open. The project interval remains $191\le a(9)\le231$. The contributor's 231 audit is saved; an independent rebuild remains pending. The contributor's 230 assembly has two outstanding premises. [231 audit](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/36-lean435-port/audit231/final-audit.txt) · [230 assembly](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/37-230-feasibility/ASSEMBLY.md) · [Published 191-edge construction](https://arxiv.org/abs/2607.15270)

The next case on the same route is to retain 80 consecutive edges of the original 22 reference parents. Compare the resulting long shapes with the full 84-edge catalogue before searching both roots of any new representative. The 80-edge census is pending. [Marked route](../../further-research/routes/ACTIVE.md) · [Other research routes](../../further-research/routes/README.md) · [Full manuscript review](review/README.md)

## Reproducing the calculation

Use the resource-limited runner from the repository root. Supply 84 or 88 to the core commands and 191 or 192 to the replay commands. The original run receipts record the exact arguments, timings and memory samples. Each command runs separately. The search scripts read the existing ledgers when resuming. [Round receipts](runs/) · [Corner search code](partners.py) · [Core-parent search code](extended.py)

~~~powershell
python -B milestones/250-corner-partners/run.py cores --core 84
python -B milestones/250-corner-partners/run.py core_audit --core 84
python -B milestones/250-corner-partners/run.py replay --target 192
python -B milestones/250-corner-partners/run.py extended --target 192 --replay
python -B milestones/250-corner-partners/compile_freed.py
~~~
