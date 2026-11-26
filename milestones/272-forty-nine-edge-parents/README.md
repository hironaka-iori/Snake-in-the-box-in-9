# Round 272 · Rebuilding an eight-dimensional arm around a 49-edge seven-dimensional snake

**The longest eight-dimensional snake obtained from the 38 specified 49-edge parents by crossing a new coordinate once has 96 edges.** Exactly eight of the 76 crossing endpoints admit a 46-edge opposite arm. They give 84 distinct eight-dimensional snakes of length 96. No endpoint in this collection admits an opposite arm of length 47 or greater. Every qualifying path is available as an ordered list of vertices. [Summary](summary.json) · [84 eight-dimensional paths](q8-arms.json)

For a 98-edge eight-dimensional snake that crosses a coordinate once, Round 270 reduced the possibilities to a split of 49 and 48 edges. The present result imposes two necessary conditions on its **49-edge arm**. That arm must use each of its seven coordinates at least twice, and it can share at most 19 consecutive edges, up to cube isometry and reversal, with any optimal seven-dimensional snake. Existence outside the enumerated family remains open. [Round 270 reduction](../270-optimal-seven-dimensional-arms/README.md) · [49-edge parents](q7-parents.json)

## Where the 38 parents come from

Paths are identified under cube translations, permutations of coordinate axes and reversal. For a transition word, number the axes in order of first appearance in each direction and select the lexicographically smaller word. This removes exactly the stated equivalences. All lengths count edges.

| Source of 49-edge seven-dimensional parents | Distinct shapes |
|---|---:|
| Trim one end of a 50-edge seven-dimensional snake | 12 |
| Retain any 40-edge interval of an optimal snake and regrow both ends to 49 | 13 |
| Retain a 32-edge interval | 14 |
| Retain a 24-edge interval | 25 |
| Retain a 20-edge interval | 27 |
| Use a coordinate exactly once | 28 |
| Add one edge to any of the 570 single-crossing 48-edge shapes | 28 |
| Recover every 49-edge interval on seven coordinates from the specified stored paths | 8 |
| Union, followed by all possible one-vertex exchanges | **38** |

The interval search starts from all six undirected 50-edge classes in Palani's classification. At length 20 these give 121 inequivalent marked intervals. For each, enumerate every legal length of the left tail and every complementary right tail that brings the full path to 49. A new vertex must touch only the current tip. Every completed path containing the marked interval can be built in this order. Reversing all 121 marked intervals and repeating the enumeration gave the same multiplicity for every output at every interval. The two orientations each visited 353,925,163 tail prefixes. [Palani, Tables 5.1–5.2](https://ai.uga.edu/sites/default/files/inline-files/theses/palani_ananta.pdf#page=54) · [Original vertices and transition words](../270-optimal-seven-dimensional-arms/palani-q7.json) · [20-edge windows and completions](parents-wide-20.json) · [Reversed-interval replay](parents-wide-20-replay.json)

For the archive search, the input comprises 1,042 ordered nine-dimensional paths of length 190, 131 of length 191, the 2,760 Round 267 eight-dimensional shapes and the 53 Round 270 shapes. Across these sources, 133 occurrences use seven coordinates in a 49-edge interval, giving eight shapes. The union in the table is closed under removing one occupied vertex and inserting any previously unoccupied vertex whenever the new induced graph is a path. Checking every exchange by both vertex degrees and the surviving path fragments gives nine components of sizes 15, 10, 3, 3, 2, 2, 1, 1 and 1. [Source occurrences](project-intervals.json) · [Seed provenance](seeds.json) · [All one-vertex exchanges](q7-parents.json)

## All long seven-dimensional snakes with a once-crossed coordinate

Cutting at the sole use of a coordinate gives two six-dimensional snakes that meet in exactly the crossing vertex when projected to the same face. With lengths $a\ge b$ and $a+1+b\ge48$, one has $a\ge24$. Translate the crossing to zero and enumerate every rooted six-dimensional snake with axes numbered by first use. Of 651,077 prefixes, 1,228 have 24 edges, 102 have 25, and one has 26. There are no longer prefixes. For each retained first arm, enumerate the opposite six-dimensional snake from zero in the same coordinates, avoiding the other vertices of the first arm, allowing all lengths up to $a$. This visits 44,532,829 opposite prefixes and emits 622 labelled pairs meeting the length requirement. Independent available-vertex and occupied-neighbour traversals agree on the full sorted lists of longer arms and labelled pairs. Each resulting path was also checked by examining all pairs of vertices. [Enumeration and exact replay](six_cube.py) · [Both traversal rules](SixCube.cs) · [Seven-dimensional shapes](q7-single-crossings.json) · [Labelled pairs](q7-layer-joins.hex.gz)

| Seven-dimensional length | 48 | 49 | 50 |
|---|---:|---:|---:|
| Distinct shapes crossing some coordinate once | 570 | 28 | 3 |

The three 50-edge outputs agree exactly with the single-crossing shapes in Palani's classification. Growing both free ends of all 570 shorter shapes gives exactly the 28 single-crossing 49-edge shapes. Seven of those 28 supply 69 of the 84 eight-dimensional paths. [Endpoint extension provenance](seeds.json)

## The opposite seven-dimensional arm

Orient each 49-edge parent $P$ from its crossing endpoint and translate that endpoint to zero. A compatible opposite path $Q$ starts at zero and satisfies $V(P)\cap V(Q)=\{0\}$. This condition accounts for every possible edge between faces, since an edge between the faces joins equal projected vertices. The eight-dimensional path has $49+1+|E(Q)|$ edges. Enumerate every $Q$ of at least 46 edges at both endpoints of all 38 parents, continuing beyond every qualifying prefix to exhaustion. The available-vertex traversal visited 364,096,527 prefixes, and the occupied-neighbour traversal visited 898,548,700. Their ordered lists of emitted paths agreed at every root. Checking all vertex pairs of each joined sequence confirmed validity. Each of the 84 labelled joins represents a different cube-isometry and reversal class. [Full primary output](partners.json) · [Per-root independent replay](partner-replay.json) · [Algorithms and pruning](../270-optimal-seven-dimensional-arms/PrimerPartners.cs)

Of the 84 shapes, 83 are absent from the union of the Round 267 and Round 271 whole-arm catalogues. Sixty-six are absent even as consecutive intervals of the corresponding earlier arms. At 67 shapes, both free tips are blocked. Extending the other 17 yields exactly the 17 previously catalogued 97-edge shapes. These 84 paths give fixed eight-dimensional arms for a nine-dimensional join. Each needs a compatible opposite arm of at least 95 edges to obtain 192. [Ordered arms and source membership](q8-arms.json) · [All free-end extensions](q8-end-extensions.json)

## Complementary 48-edge arm

The 570 single-crossing 48-edge parents have 1,140 distinct orientations after rooted coordinate normalization. The stored partition has 382 groups. Each group shares at least 45 occupied nonzero vertices, so a 49-edge opposite arm for any group member must avoid every vertex of the common set. The available-vertex traversal exhausted the first 45 groups, covering 145 rooted orientations of 138 shapes. Across 297,081,459 prefixes it found no 49-edge opposite path even under this relaxed condition. The other 337 groups and the independent replay of this partial calculation remain open. The 84-arm catalogue above is complete for its 38 fixed 49-edge parents, independently of this complementary calculation. [Group membership](short-arm-groups.json) · [Partial enumeration](short-arm-mask.json) · [Continuation program](short_arm.py)

## Reproduction and data format

Use the [guarded runner](../256-two-exchange-parents/run.py) on each script in this directory. The primary outputs are linked above. The exact execution records are in [runs](runs/).

1. Obtain the optimal-parent windows with `parents.py --window 40`, `parents.py --window 32`, `window_tails.py --window 24`, `window_tails.py --window 20`, and `window_tails.py --window 20 --reverse`.
2. Run `archive.py`, then `six_cube.py mask` and `six_cube.py contacts`. Run `seeds.py` and `exchange.py seeds.json`.
3. Run `partners.py q7-parents.json mask`, `partners.py q7-parents.json array`, then `summarize.py`. For the separate shorter-arm calculation, `short_arm.py groups` generates the partition and `short_arm.py mask --count 45` processes the first 45 pending groups.
4. In `q8-arms.json`, each key is the canonical transition word in hexadecimal, one byte per coordinate index. Each record gives `joined_q8` as an ordered eight-dimensional vertex list, `parent49` and `partner` as the two seven-dimensional vertex lists directed from the crossing, and `parent49_key` and `crossing_end` identify the rooted parent. The SHA-256 digest of this arm file is `18e39f9bab15d0875dd55326cfc8208898194a15e6e948d65c8921689b4731ed`.
