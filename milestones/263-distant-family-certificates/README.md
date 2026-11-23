# Round 263 · Can a distant-reference arm join to 192 edges?

All 21 previously unresolved 96-edge arms exclude a 95-edge partner at both ends. Together with eight earlier exclusions, this accounts for all 29 shapes at exchange distances two and three from the distant reference. The replay accounted for all 294 possible first steps at the 42 endpoints.

| Replacements in the reference's 48-site smaller class | Possible 96-edge shapes | Both endpoints excluded before this round series | Both endpoints excluded now |
|---:|---:|---:|---:|
| Exactly two | 14 | 5 | 14 |
| Exactly three | 15 | 3 | 15 |

## How one proof covers several parents

Translate the joining endpoint to zero. For a group of parents let \(F\) be their common forbidden set and let \(E_i\) contain the additional forbidden sites of parent \(i\). A rooted partner avoiding \(F\) is compatible with some parent precisely when its vertices contain no set meeting every \(E_i\). It suffices to forbid the inclusion-minimal sets meeting them all. The implementation compared these clauses with an explicit choice of parent on all 266,869 assignments to the variable sites, counted over the recorded families. A second constraint uses earlier certificates. If every 95-edge partner must hit a set \(S\), a partner avoiding \(F\) must hit \(S\setminus F\). The coordinates, source and image of every retained positive clause were checked. [Construction of the families](family.py) · [Adaptive grouping](cover.py) · [Lean implications](Compatibility263.lean) · [Lean compiler and axioms](Compatibility263-compile.json)

The rooted path has 48 vertices of each parity, degree one at the crossing and the free endpoint, and degree two at every other selected vertex. Every induced 95-edge path satisfies these constraints. Each numerical exclusion has a checked contradiction against its reconstructed formula, or uses a previously certified set contained in the parent's forbidden sites. When the root was split, coverage was computed separately for every legal first edge of each actual parent. An inconclusive broad query could therefore be settled by its subfamilies or first steps. [Cases, formulas and proof records](decisions.json) · [Compressed certificates](proofs/) · [Independent reconstruction and coverage](summary.json)

The replay checked 40 distinct contradiction certificates. Each already gives a contradiction using the degree, parity, face and compatibility constraints before any disconnected cycles are removed. The 24 queries that reached a time limit contribute no exclusion. The initial attempt to send an empty positive clause to the proof checker was discarded. In that case, direct containment of the Round 262 obstruction supplies the proof. [Replay program](audit.py) · [Round 262 replay](../262-common-forbidden-sites/replay.json)

## Consequence for a 96-edge window

The earlier calculation excluded distances zero and one from the distant reference. Across its 29 shapes at distances two and three, direct enumeration of all endpoint neighbours gives just one extension. It leads to the 97-edge shape beginning \(\mathtt{f57caef5}\), which cannot extend to 98 and has a separate 192-edge exclusion at both ends. Thus an excluded 96-edge shape cannot reappear as a proper segment of a longer successful parent. An overlap of at least 45 of the 48 smaller-class sites with this reference would require replacing at most three. The overlap is therefore at most 44 in every isometric placement. [Original shell and extensions](../257-three-exchange-parents/summary.json) · [97-edge endpoint certificates](../252-shorter-reference-segments/replay-68-192.json)

The global interval remains \(191\leq a(9)\leq230\). The explicit 191-edge witness passed all 18,336 pair comparisons. These four rounds concern paths crossing one coordinate exactly once. The contributor's global upper bound has a saved interface audit at the pinned revision. A fresh independent rebuild remains pending. [Global witness](../../outputs/snake9_witness.json) · [Contributor audit](contributor.json) · [Reviewed manuscripts](manuscripts.json)
