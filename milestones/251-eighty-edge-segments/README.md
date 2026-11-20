# Round 251 · One-crossing joins retaining 72 reference edges

**The exact maximum is 191 edges when an arm of at least 96 edges contains 72 consecutive edges of one of the 22 reference paths.** The paths meet across one edge between two eight-dimensional faces. We allow both ends of the long arm to change and the entire opposite arm to vary. Of the 28 possible long-arm shapes in this family, exactly five attain 191. The three new shapes all have 96 edges. Each excludes a 94-edge partner at both endpoints. The global nine-dimensional maximum remains open. [Complete 72-edge census](census-72.json) · [Six rooted exclusions](replay-census-72-192.json) · [Five 191-edge constructions](../248-rooted-arm-capacity/README.md)

## Which long arms can grow out of a reference segment?

The 22 reference paths are the fifteen original long parents and the seven obtained by legal interior corner changes. A shape is identified up to coordinate permutation, translation and reversal. An occurrence specifies both the reference path and a starting index. A segment preserves the order of consecutive edges. [Original parents](../248-rooted-arm-capacity/parents.json) · [Corner changes](../249-long-parent-joins/geometry.json)

| Edges retained | Occurrences | Distinct segment shapes | Distinct completions with 96–98 edges |
|---:|---:|---:|---:|
| 84 | 293 | 134 | 25 |
| 80 | 381 | 165 | 25 |
| 76 | 469 | 189 | 25 |
| 72 | 557 | 205 | 28 |

An induced path extends at an endpoint exactly when the new vertex is unused, neighbours that endpoint, and has no other neighbour in the existing path. The first enumeration grows the left and then the right portion of every segment. Any valid completion has such an ordering. The second extends either end at each step and merges isometric paths after each edge. It starts independently from every labelled occurrence. The sets of shape identifiers agree separately at lengths 96, 97 and 98. At 72 they give 22, five and one class, respectively. The eight-dimensional maximum of 98 bounds the enumeration. [Two enumeration methods](census.py) · [80-edge census](census-80.json) · [76-edge census](census-76.json) · [Earlier 84-edge census](../250-corner-partners/core-audit-84.json)

| New parent (hash prefix) | Source of retained 72-edge segment | Start in source | Edges added left and right | Endpoints | Longest match with any reference |
|---|---|---:|---|---|---:|
| f0fcfd23 | donor 15 | 0 | 0 and 24 | 0 and 78 | 75 |
| 460cdd57 | donor 15 | 2 | 22 and 2 | 78 and 72 | 74 |
| ff535588 | donor 16 changed at position 72 | 1 | 22 and 2 | 78 and 72 | 74 |

Every retained segment longer than 72 contains a 72-edge segment. Comparing all segments of the three new shapes with the references therefore gives the intermediate counts exactly. There are 25 long completions for every retained length from 76 through 84, 26 at 75, and 28 at every length from 72 through 74. The three ordered paths and their provenance are saved in the [complete census](census-72.json).

## Can any of the three additional parents reach 192?

With the joining endpoints identified in projection, opposite-face arms are compatible exactly when their projected vertex sets share only that endpoint. A join has the sum of the arm lengths plus one edge. At each of the six roots of the new parents, the complete partner formula for 94 edges gives a contradiction. Where applicable, a checked older cap supplies a necessary clause requiring a visit to one of the vertices freed by changing the parent. Each such clause was checked against the explicit coordinate map, the full placed parent and its archived rooted cap. The other endpoint of the proposed partner was free. All six compressed LRAT certificates were replayed against regenerated formulas.

A 95-edge or longer partner has a 94-edge prefix at the same root. Thus the six exclusions settle both 191 and 192 for the three new parents. Combining them with the earlier 25-parent result proves the stated maximum. Every 192-edge single-crossing snake must avoid the 205 reference segments in every arm of at least 96 edges. [Search and geometric restrictions](partners-census-72.json) · [Certificate replay](replay-census-72-192.json) · [Earlier 25-parent result](../250-corner-partners/README.md)

## Reusing a donor segment versus building a partner

For each new root we computed the longest partner obtainable by taking one contiguous segment of any of the 903 archived eight-dimensional donor paths. All starting positions, directions and coordinate permutations were allowed. Translation is determined by the joining endpoint. The donor maxima are exact. The last column concerns arbitrary partners and reports verified lower and upper bounds.

| Parent | Root | Exact longest donor segment | Unrestricted partner length |
|---|---:|---:|---:|
| f0fcfd23 | 0 | 37 | 82–91 |
| f0fcfd23 | 78 | 42 | 70–93 |
| 460cdd57 | 78 | 36 | 75–91 |
| 460cdd57 | 72 | 33 | 74–93 |
| ff535588 | 78 | 39 | 72–93 |
| ff535588 | 72 | 34 | 84–93 |

The segment computation checks all $8!=40{,}320$ axis maps. For each root, it records an attaining donor, start, direction, coordinate map and ordered join. At one edge beyond each maximum a second computation places the parent against an independently constructed index of forbidden donor vertices. Every placement fails. Longer donor segments would contain a prefix of this excluded length. At the last root, for example, there are 108,000 oriented occurrences of length 35, comprising 5,646 distinct rooted transition words. None fits. A separately constructed 84-edge partner gives a 181-edge join at that same root. Its 182 vertices passed all 16,471 pair comparisons. Thus even the first 35 edges of that partner cannot be a segment from the donor bank at the specified root. [Exact maxima and direct enumeration](bank_capacity.py) · [35-edge exclusion and 34-edge witness](bank-capacity-2-1.json) · [Independent placement algorithm](bank.py) · [Unrestricted witnesses and independent next-length checks](regrowth-witnesses.json)

The unrestricted upper bounds use six original proofs and two additional certificates for 92-edge partners. The latter lower the cap to 91 at the first root of each of the first two shapes. Shorter searches with a time limit left gaps. Every number in the lower-bound column comes from an ordered nine-dimensional path checked against every pair of vertices. [Additional search ledger](profiles.json) · [Proof replay](profile-audit.json) · [Proof archives](proofs/)

## A bound applied partway along a partner

Suppose the partner has already traversed $t$ edges and stands at $v$. Place an old parent with root $v$ and verified partner cap $c$. If the full partner has more than $t+c$ edges, it must visit one of the old parent's vertices outside the current parent, other than $v$, during the next $c+1$ edges. Otherwise the next $c+1$ edges form a partner for the old parent. Distinctness and the absence of chords also imply that future vertices avoid the closed neighbourhood of every vertex strictly before the cut. Lean checked these implications with the old cap as a premise. [Lean source](Suffix251.lean) · [Compiler and axiom receipt](Suffix251-compile.json)

For parent 460cdd57, a proposed 95-edge partner beginning at 72 can reach 0 via 64 or 8. From 0 it would still require 93 edges. The saved 98-edge parent's cap at 0 is 88; the only exceptional vertices in this placement are 1 and 73. Vertex 73 would touch the earlier vertex 72, and 1 touches 0, so the next vertex must be 1. That eliminates five otherwise legal steps after each prefix. At root 78 of two other rooted cases the same reasoning forces 73 after either of two prefixes. The independent check recovered all fourteen excluded three-edge prefixes. Other prefixes survive this geometric calculation and are covered by the full endpoint certificates above. [Search of local prefixes](suffix-72-192-d3-w24.json) · [Independent replay](suffix-replay-72-192.json)

## Global status and verification

The project interval is $191\le a(9)\le231$. The collaborator's saved audit verifies the 231 assembly at the reviewed revision. An independent full dependency rebuild remains pending. The 230 assembly still has open premises. The 72-edge calculation applies to the specified single-crossing family. [Published 191-edge construction](https://arxiv.org/abs/2607.15270) · [Contributor audit for 231](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/36-lean435-port/audit231/final-audit.txt) · [230 assembly](https://github.com/hironaka-iori/Snake-in-the-box-in-9/blob/e0ddaefcd2cc520c9fa81ef2df37f49952e6656d/milestones/37-230-feasibility/ASSEMBLY.md)

The guarded run records include the exact arguments, timings and resource observations. The full manuscript and short explanation were rebuilt from their authoritative sources. [Execution receipts](runs/) · [Full manuscript build](snake9_research-receipt.json) · [Short explanation build](snake9_frontier_explanation-receipt.json) · [Manuscript verification](manuscripts.json) · [Active route](../../further-research/routes/ACTIVE.md)
