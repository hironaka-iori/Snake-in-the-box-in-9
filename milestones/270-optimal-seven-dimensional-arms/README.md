# Round 270 · Eight-dimensional arms built from optimal seven-dimensional paths

**The maximum is 97 edges for an eight-dimensional snake that crosses a chosen coordinate exactly once and has a 50-edge seven-dimensional arm on one side.** Up to cube isometry and path reversal, the census contains 36 shapes of length 96 and 17 of length 97. One endpoint of one seven-dimensional shape supplies all 17 longest constructions. All 53 shapes were absent from the Round 267 collection and were available as fixed arms for nine-dimensional reconstruction. [Census summary](q7-primer-summary.json) · [All 53 paths and their seven-dimensional partners](q8-primer-arms.json)

In nine dimensions, rebuilding the opposite arm at one fixed 96-edge parent improved its verified join from 144 to 187. [Nine-dimensional search](Q9-CONSTRUCTIONS.md) · [Ordered 187-edge snake](best-187.json)

## Seven-dimensional primers

Palani's Tables 5.1 and 5.2 give the twelve directed classes of longest seven-dimensional snakes. Each has 50 edges. We recovered all twelve transition words from Table 5.1 and independently recovered their vertex sequences from the two pages of Table 5.2. The sequences agree at every position. Reversing the path and renaming its coordinate axes pairs rows 1 and 5, 2 and 6, 3 and 4, 7 and 10, 8 and 11, and 9 and 12. There are thus six shapes with two possible crossing endpoints each. The enumeration uses this published classification for completeness of the primer list. [Palani, *An Analysis of Hypercube Space for Solving the Snake-In-The-Box Problem*, Tables 5.1–5.2](https://ai.uga.edu/sites/default/files/inline-files/theses/palani_ananta.pdf#page=54) · [Recovered words, vertices and reversal pairs](palani-q7.json) · [Table extraction](extract_palani.py)

Translate the crossing endpoint to zero in both seven-dimensional faces. If the fixed path is $P$, the other path must begin at zero and avoid $P\setminus\{0\}$. These are exactly the conditions that prevent a second edge between the two faces. A partner of length $b$ gives an eight-dimensional path of length $51+b$. The targets 96, 97 and 98 therefore require partners of 45, 46 and 47 edges respectively.

The first traversal stores two 64-bit words for the seven-dimensional vertices still available. When it selects a neighbour of the tip, it removes all neighbours of the old tip from subsequent choices. The second traversal maintains the number of occupied neighbours of each site. It steps only to unused vertices touching the current path exactly once. Both traversals sometimes count reachable vertices of each parity. A branch can be pruned when that component has too few even or odd sites to reach 45 edges. After reaching 45 edges, the traversal emits the current path and continues to every legal extension. This gives an upper bound at each primer endpoint without assuming the eight-dimensional optimum. [Native traversals](PrimerPartners.cs) · [Partition into first steps and verification of both traversals](primer_census.py) · [Combined verification](all_primers.py)

## Census by crossing endpoint

The two traversals returned identical ordered partners in all 72 first-step cases. In the table, ends 0 and 1 denote the first and last vertices in the printed orientation of the representative row. A zero in a 45-edge column rules out all longer partners at that endpoint. The search did not determine its longest partner below 45. [Per-endpoint counts and replay records](q7-primer-summary.json)

| Palani row | Reversed row | End 0, 45 edges | End 0, 46 edges | End 1, 45 edges | End 1, 46 edges |
|---:|---:|---:|---:|---:|---:|
| 1 | 5 | 0 | 0 | 0 | 0 |
| 2 | 6 | 0 | 0 | 0 | 0 |
| 3 | 4 | 0 | 0 | 0 | 0 |
| 10 | 7 | 0 | 0 | 23 | 17 |
| 8 | 11 | 5 | 0 | 4 | 0 |
| 9 | 12 | 0 | 0 | 4 | 0 |

Four of the twelve crossing endpoints produce an eight-dimensional snake with at least 96 edges. Only the last vertex of row 10 allows a 46-edge partner, and no endpoint allows 47. The complete list of 53 labelled pairs also gives 53 distinct eight-dimensional shapes after canonicalization. [Eight-dimensional paths and endpoint assignments](q8-primer-arms.json)

## Previously published 97-edge arms

Casella's 186-edge nine-dimensional example and Bitterman's 182-edge example both begin with a 97-edge eight-dimensional arm. Each word crosses the ninth coordinate once. Their other eight-dimensional arms have 88 and 84 edges respectively. We also recovered eight-dimensional paths from Bitterman's Appendix D.2 and the first 98 vertices of Atluri's displayed sequence. Atluri's following vertex would introduce chords to the vertices at indices 45 and 75, counting from zero. We use the verified 97-edge prefix. [Casella, Appendix A.1](https://www.ai.uga.edu/sites/default/files/inline-files/theses/casella_darren.pdf) · [Bitterman, Appendix D](https://openscholar.uga.edu/record/19672) · [Atluri, displayed node sequence](https://openscholar.uga.edu/record/21280) · [Primary-source transcriptions and hashes](uga270.json)

Up to cube isometries and path reversal, the 21 historical observations give 18 distinct 97-edge shapes. Seventeen contain the same 50-edge seven-dimensional primer from row 10 of Palani's Table 5.1. The census recovers exactly these 17. Every one uses its least frequent coordinate once and has endpoints at Hamming distance five. The remaining shape, Bitterman D.2 example 18, uses its least frequent coordinate twice and has endpoint distance three. For comparison, two of the seven Round 267 shapes of length 97 have minimum coordinate use three and endpoint distance five. Four have minimum use four and distance five, and one has minimum use four and distance three. [Counts from canonical transitions](q7-primer-summary.json) · [Earlier eight-dimensional collection](../267-fixed-arm-extensions/donors.json) · [Full 186- and 182-edge nine-dimensional controls](historical-q9-controls.json)

Thirteen of the 36 length-96 shapes occur as consecutive segments of the 18 historical length-97 shapes. The other 23 occur in neither the Round 267 collection nor those historical segments. Examining every possible extra edge at both free ends of all 53 shapes gives exactly the 17 known length-97 shapes. Those 13 length-96 shapes can therefore grow at an endpoint, while both endpoints are blocked in the other 23 length-96 shapes and in all 17 length-97 shapes. [Published segments associated with each path](q8-primer-arms.json) · [Endpoint extension by coordinate](q8-end-extensions.json)

Kinny reported that a 50-edge seven-dimensional primer can grow to a 97-edge eight-dimensional snake and that no optimal seven-dimensional primer can grow to 98. The present search records every partner in the specified single-crossing construction, including all its 96-edge outputs. [Kinny, *A New Approach to the Snake-In-The-Box Problem*, Section 4](https://ebooks.iospress.nl/pdf/doi/10.3233/978-1-61499-098-7-462)

## Scope

**Any 98-edge eight-dimensional snake that crosses a coordinate exactly once must split there into seven-dimensional arms of 49 and 48 edges.** The arms sum to $98-1=97$, and Palani's complete seven-dimensional classification bounds each arm by 50. The only unordered length pairs are $(50,47)$ and $(49,48)$. The census excludes $(50,47)$ at every possible crossing endpoint. Existence for $(49,48)$ remains open in this calculation. At length 97 the possible pairs are $(50,46)$, $(49,47)$ and $(48,48)$, of which the census resolves $(50,46)$. Eight-dimensional paths may use every coordinate more than once, as Bitterman D.2 example 18 does. [Palani, Tables 5.1–5.2](https://ai.uga.edu/sites/default/files/inline-files/theses/palani_ananta.pdf#page=54) · [Enumeration of all published optimal primer shapes](q7-primer-summary.json)

To reproduce the computation, use the guarded runner from [Round 256](../256-two-exchange-parents/run.py) on `all_primers.py census`, then `all_primers.py audit`, then `all_primers.py summarize`. Each complete shard records its ordered partners as hexadecimal strings, one byte per seven-dimensional vertex. The hash covers the uncompressed, sorted list. Each complete second traversal must match every emitted path from the first traversal exactly.

