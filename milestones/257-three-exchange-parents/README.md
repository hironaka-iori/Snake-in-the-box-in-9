# Round 257 · Three simultaneous parity exchanges

Every consecutive 96-edge window of either arm of a single-crossing snake of at least 192 edges must omit **at least four** of the 48 smaller-class sites of each of the six references in the attaining component, under every cube isometry. Its smaller class overlaps each reference on **at most 44** sites. A separate reference outside this component behaves differently.

## The six reference arms

Hold one labelled smaller class fixed as the reference, remove any three of its 48 sites and insert any three of the remaining 80 sites of the same parity. The final path must have 96 edges. Both endpoints, the entire traversal and the other 49 sites are free. There are \(\binom{48}{3}\binom{80}{3}=1{,}421{,}039{,}360\) candidate sets per reference, or 8,526,236,160 reference and candidate pairs for the six arms. A set shared by different reference searches is counted once in each.

| Reference | Classes passing the physical-neighbour count | Classes admitting a path | Labelled paths |
|---|---:|---:|---:|
| 0 | 470 | 0 | 0 |
| 3 | 470 | 0 | 0 |
| 4 | 862 | 1 | 1 |
| 5 | 470 | 0 | 0 |
| 8 | 470 | 0 | 0 |
| Sixth reference | 734 | 0 | 0 |

The unique positive case removes \(47,69,94\) and inserts \(37,62,79\), in the archived labelling of reference 4. Interchanging coordinate indices 5 and 6 (numbered from zero) maps the **entire ordered original arm** onto the returned path. Its endpoints change from \(0,36\) to \(0,68\). Thus a labelled exchange that changes three sites need not produce a different shape. [Explicit path](shell-4.json)

The monotonicity and connector argument from [Round 256](../256-two-exchange-parents/README.md) applies to each of the three insertions. The first implementation uses integer bit sets to update opposite-site counts and enumerates spanning orders and their labels. The independent implementation counts neighbours directly and selects all connected spanning degree-two graphs through the auxiliary endpoint vertex. Their lists of labelled paths agree. [Triple enumeration](three_exchange.py) · [Independent replay](replay.json)

All six shapes were already mutually reachable by single exchanges. The two- and three-exchange results prove that even arbitrarily many exchanges of up to three vertices at a time cannot leave the six. The restricted maximum with an unrestricted opposite arm is exactly 191. If a window in a proposed single-crossing snake shared at least 45 smaller-class sites with one reference, its shape would belong to the six. As an entire arm it violates the known join ceiling. A proper window could grow by one edge in its face, contrary to the exhaustive endpoint checks. This proves the 44-site ceiling.

## A different reference

For the Round 254 reference beginning \(\mathtt{e6e522b8}\), exactly two exchanges yield 14 labelled paths on six viable classes. They give 14 shapes. Exactly three exchanges yield 15 labelled paths on six viable classes, giving 15 other shapes. The two lists are disjoint. All 14 two-exchange shapes belong to the previously known 41-shape one-exchange component. Among the 15 three-exchange shapes, 13 belong to that component and two belong to the earlier 264-shape catalogue outside it. These two shapes show that the three-exchange move can leave a one-exchange component, even though the same move preserves the six attaining shapes. All counts here describe a single move from the distant reference. [Two exchanges](two-exchange-comparison/shell-distant.json) · [Two-exchange replay](two-exchange-comparison/replay.json) · [Three exchanges](shell-distant.json)

The 44-site ceiling applies to the six references in the first table. The distant reference still has its separate 46-site ceiling established in Round 255.

## Constructing a partner

At both possible crossings of each of the 29 distant-shell shapes, allow the partner to begin with any directed 51-edge segment of any of 95 donor shapes, in any coordinate placement. After those edges the partner may follow any induced continuation in the allowed face. The donor shapes include earlier attaining partners, reconstructed 95-edge paths and partners constructed at other roots. The enumeration identified 2,074 rooted segment words up to coordinate relabelling and considered every one of the \(8!\) root-preserving permutations. Exactly 61 placed prefixes fit, across 34 of the 58 roots.

From each prefix a complete search grew the free end. A first implementation blocked neighbours of earlier vertices using bit sets. A second counted neighbours of the selected path directly, requiring exactly one for every added vertex. They agreed on the maximum and number of visited prefixes in all 61 cases (247,631 continuation nodes in total). The restricted maximum was **178 edges**. Two roots attain it with an 81-edge partner. An explicit 179-vertex witness passed all 15,931 pair comparisons. Starting with 72 donor edges gives the same maximum with 41 placed prefixes across 23 roots. [51-edge prefixes and continuations](constructed-51.json) · [72-edge comparison](constructed.json) · [Explicit witness](best-join.json)

Lean checked that a vertex on an induced path in a simple undirected graph has at most two selected neighbours. It also checked the insertion condition used by the search. Before inserting an eventual internal vertex, it must already have two distinct candidate neighbours, each adjacent to at most one previously selected site. The finite cube enumerations and partner maxima use separate native verification. [Lean source](Supply257.lean) · [Compiler and axiom receipt](Supply257-compile.json)

## Unrestricted opposite arms and proper windows

A separate calculation allowed an arbitrary 95-edge partner. Among 50 selected rooted parents it excludes 13 roots, and 37 remain open. Two certificates were inherited. The new contradiction archives and inherited restrictions were replayed against the saved inputs. A broad prefix search was interrupted when free memory fell below the project reserve. Its saved cases were replayed, and a smaller follow-up completed within the resource limits. A timed-out case contributes no exclusion. Taking earlier results into account, five of the 14 two-exchange shapes and three of the 15 three-exchange shapes now exclude 192 at both ends. Nine and twelve shapes, respectively, remain unresolved. Two of the previous 29 open shapes in the 41-shape component now have exclusions at both ends. [Root-by-root replay](partner-replay-95.json) · [Remaining shapes and proof dependencies](summary.json)

Both shapes outside the 41-shape component are excluded even as proper windows. Only one of the 29 arms has a one-edge extension in \(Q_8\). It extends in exactly one way to a 97-edge shape beginning \(\mathtt{f57caef5}\), which has no extension to 98. The earlier unrestricted partner certificates exclude 192 at both ends of that 97-edge shape. Therefore placing the extendible 96-edge arm inside a longer arm also cannot give the desired join. [Extended vertex sequence and earlier root records](summary.json) · [Round 252 certificate replay](../252-shorter-reference-segments/replay-68-192.json)

The reviewed global interval is \(191\le a(9)\le230\). The explicit lower-bound sequence passed all 18,336 pair comparisons. The contributor's saved interface audit establishes its 230-edge theorem for every snake in \(Q_9\). Its full dependency chain was not independently rebuilt in these two rounds. [Explicit 191-edge witness](../../outputs/snake9_witness.json) · [Contributor theorem and audit](contributor.json)
