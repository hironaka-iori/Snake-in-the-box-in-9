# Round 260 · How far the nearest 95-edge donor is from a 192-edge join

At the 42 endpoints of the 21 unresolved distant-reference parents, every placement in the specified 95-edge donor catalogue has at least seven common vertices with the parent **in addition to the crossing**. The bound of seven is attained at five endpoints. All 42 parent arms have 96 edges. In a one-crossing join with a 95-edge partner, each extra common vertex creates an edge between the two faces that joins nonconsecutive vertices.

| Minimum extra common vertices at an endpoint | Endpoints |
|---:|---:|
| 7 | 5 |
| 8 | 12 |
| 9 | 16 |
| 10 | 3 |
| 11 | 3 |
| 12 | 3 |

The source collection consists of 270 distinct arms of lengths 96 through 98 and the earlier 72 shapes of length 95. Every directed segment of length 95 was taken. Normalising the coordinate labels in first-use order left 1,008 rooted transition sequences. Each uses all eight directions. Translating its first vertex to the parent's endpoint fixes the translation, and all \(8!=40{,}320\) coordinate permutations remain. This gives 40,642,560 placements per endpoint and 1,706,987,520 endpoint–placement pairs. Counts are per labelled parent endpoint. There are 189 minimising placements across the 42 endpoints. [Donors, segment origins and reference arms](catalogue.json) · [All minima and attaining permutations](minimum.json)

In one attaining placement the extra common vertices are \(24,29,31,134,139,210,222\). Checking its ordered 192-edge walk gives exactly the seven chords \((v,v+256)\) at these vertices. [Explicit closest pair and chord list](closest-pair.json)

The first calculation maintained sets of coordinate permutations giving precisely \(j\) common vertices along a growing donor prefix. The second computed the full binary sum of the 95 intersection indicators for each placement. It independently ruled out every smaller count and reproduced the entire list of minimisers. Every reported minimiser was also placed directly and its intersection recomputed. [Prefix calculation](census.py) · [Binary-sum replay](replay.py) · [Replay results](replay.json)

With the parent and its crossing fixed, a 95-edge partner derived from any one placed donor must omit every extra common vertex. Thus at least seven of that donor's vertices must change, and the table gives the stronger requirement at each endpoint. This argument concerns the specified catalogue. A different partner can have a different vertex set and a different transition sequence. [Remaining parent cases from Round 257](../257-three-exchange-parents/summary.json)

The scheduled ten-round manuscript review compares both sources with the previous complete reading at Round 250 and includes the Round 263 publication addendum. [Written-source review](review/README.md)
