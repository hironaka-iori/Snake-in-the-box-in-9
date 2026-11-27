# Round 278 · Rebuilding outer arms around a retained interval

**The exact maximum is 191 edges** for a nine-dimensional snake that crosses a coordinate exactly twice and has one of the 22 middle shapes extracted from the archived 190- and 191-edge snakes. Both outer arms may change in their entirety, including their lengths and endpoints. The archived paths give 625 occurrences of these 22 middle shapes. Explicit archived paths attain 191. [Proof coverage by shape, endpoint parity and port](all-middle-port-coverage.json) · [Literal archive witnesses and independent formula audit](whole-middle-witnesses.json)

For a hypothetical 192-edge snake in the full nine-cube, the longest consecutive segment it could share with an archived path has at most **153 edges for every one of the 131 archived 191s**, and **159 edges for every one of the 1,042 archived 190s**. Coordinate permutations, translation and path reversal are allowed. Each number is an upper bound on possible overlap. [All 1,173 per-path bounds and certificate occurrences](consecutive-overlap.json)

## Which middle paths can attain 192?

A twice-used coordinate cuts a snake into a middle in one eight-dimensional face and two outer arms in the other. The archives contain 537 choices of such a coordinate in 527 paths of length 190 and 88 choices in 88 paths of length 191. Up to cube symmetries and reversal, their middles have 22 shapes and lengths from 92 through 95.

The most frequent 95-edge middle occurs in 523 charts, including 84 of the 191-edge records. Its two-crossing maximum is exactly 191. It is the literal 96-vertex middle whose target-192 calculation ended open in Round 188. Matching the old coordinate order to the new one by the permutation $(0,3,2,1,4,6,7,5)$ followed by XOR with 65 recovers every vertex. The 93- and 92-edge middles accounting for the other four twice-crossed 191s also have exact maximum 191. [Earlier problem](../188-dimensional-constructions/data/lift8to9-fixed95.json) · [Why the model covers both unrestricted outer arms](WHOLE-MIDDLE-AUDIT.md) · [92-edge port partition](port-190-418-replay.json)

The selection model fixes the middle and its two crossing edges. Both endpoints of the joined path lie in the lower face. Their parity determines how many vertices of each colour that face must contain. Each port already has one edge to the middle. A checked exclusion in both possible endpoint parities rules out 192. A longer path could be shortened to 192 by removing free outer vertices. Where a whole parity query remained open, the proof partitions by the first neighbour of one port and allows the arm to be empty when its parity permits. [Whole-face formulas and proof files](whole-middle.json) · [Exhaustive port replay](port_all278.py) · [Sources and capacities](METHOD.md)

## Constructions and their limits

| Retained part | Freedom in the rest of the path | Result |
|---|---|---|
| A two-crossing middle and a short outer arm of at most three edges, in all 49 eligible archived charts | The opposite outer arm is unrestricted | Five of the 22 fixed configurations have maximum 191. The other seventeen have maximum 190. |
| The preceding fixed parts in sixteen archived 190-edge charts | Replace only the longer outer arm | Thirty ordered replacements reach nine archived 191-edge shapes. |
| One of the three new Round 277 arms of length 96 | Choose either endpoint as a single crossing and rebuild the opposite arm | The best construction has 181 edges. All six endpoints rule out 192. |
| Any of the eleven 96-edge Round 277 shapes as an interval of either arm | Allow the interval position, the crossing endpoint and the whole opposite arm to vary | A one-crossing join has at most 191 edges. |

[Exact short-arm results](FIXED-SHORT.md) · [All 30 replacements in original coordinates](fixed-short/short-donor-upgrades.json) · [Six single-crossing constructions](one-crossing/single-placements.json) · [Coverage for all eleven intervals](remaining-one-crossing/interval-coverage.json)

For a direct two-crossing comparison, a finite donor placement and alternating regrowth procedure produced joined lengths 149, 150 and 146 at the three new 96-edge middles, 153 at the published 98-edge middle, and 156 at a selected 97-edge middle. The original ordered paths are available for all five. These witness lengths give lower bounds for the specified middles. [Donor placements](lift-placements.json)

## How the overlap bound was checked

When a path contains every vertex of a specified consecutive interval, its internal vertices already have both neighbours. Any extension must grow from its two ends. The full-cube calculation allows either new tail to use any of the nine coordinates. It applies even to paths with additional crossings. Two independent searches fix different orders of growth. A complementary calculation enumerates each tail on its own and joins pairs with the right total length. A pair fits exactly when no new vertex on one tail coincides with or neighbours a new vertex on the other. Every upper bound uses complete searches only. [Two-ended enumeration](grow.py) · [Independent replay](replay.py) · [Target-specific proof](target.py) · [Compatible tail pairs](paired_intervals.py)

For each original archive path, the final calculation checks that every window one edge longer than its reported bound contains a certified impossible subpath. The comparison reconstructs a literal cube isometry at each retained certificate occurrence. Increasing the allowed changes can leave a branch open. Its time or node allowance gives no exclusion. [Interval coverage](overlap.py) · [Numerical summary](conclusions.json) · [Methods and reproduction](METHOD.md) · [Guarded run receipts](runs) · [Completion record and interrupted runs](completion.json)

No 192-edge witness was obtained. The reviewed global interval remains $191\leq a(9)\leq 230$. The upper bound comes from the contributor's audited theorem. A fresh independent rebuild of its entire dependency chain remains pending. [Contributor audit](../272-forty-nine-edge-parents/contributor.json) · [Manuscript receipts](manuscripts.json)
