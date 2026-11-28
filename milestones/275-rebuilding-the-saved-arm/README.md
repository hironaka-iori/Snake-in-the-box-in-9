# Round 275. Rebuilding the saved 189-edge snake

**The exact maximum at the saved 93-edge arm and crossing is 189.** A 95-edge opposite arm attains it. A 96-edge opposite arm is impossible even when it can use the entire opposite face. Six contradictions at a first step and six at a second step cover every possible beginning at this crossing. The related 93-edge arm that enters the same long segment from the other end also has exact maximum 189. [Original-coordinate witnesses](constructions.json) · [Unrestricted bounds and coverage](summary.json) · [Definitions and verification](METHOD.md)

**Changing sites on both sides gives a route from the saved 189 to a 191.** The example below ends at archived snake 191-52. The first step keeps the crossing vertex 44 and the entire 95-edge opposite arm. The final path uses every coordinate at least twice. All four ordered paths use the same original nine-dimensional coordinates, with every pair of vertices verified. [Complete path after each change](example-chain.json) · [Twenty destinations reachable from this starting path](chains-to-191.json)

| Length before | Sites removed | Sites added | Length after |
| ---: | --- | --- | ---: |
| 189 | 41, 45 | 104, 108 | 189 |
| 189 | 8, 304 | 41, 56, 256 | 190 |
| 190 | 300 | 12, 430 | 191 |

## How much freedom is needed for 192?

The four starting 189-edge snakes produced ten distinct 190-edge shapes by omitting at most two original sites, permitting arbitrary new sites and traversal order. Six have a once-crossed coordinate and four use every coordinate at least twice. All ten match complete snakes in the 190-edge archive.

Continuing from all ten shapes with the same freedom produced 22 distinct 191-edge snakes. Four of the ten starts produced all 22, including 19 with no once-crossed coordinate. Each is equivalent to an archived 191. The two-site search did not reach 192 from any of the four 189s, ten 190s or 22 recovered 191s. [First repairs](whole-path-repairs.json) · [190-to-191 continuations](growth-from-190.json) · [Complete archive comparison](classified.json)

| Starting length | Starting shapes | Omission patterns per shape | Total patterns, independently checked | Longer lengths reached through 192 |
| ---: | ---: | ---: | ---: | --- |
| 189 | 4 | 18,146 | 72,584 | 190 |
| 190 | 10 | 18,337 | 183,370 | 191 |
| 191 | 22 | 18,529 | 407,638 | None |

For each of the 22 recovered 191-edge shapes, the two enumerations also checked every single interval of three through ten omitted positions, giving 32,824 further choices. No 192-edge snake resulted. Consequently, a 192-edge snake retaining all but a single interval of sites of one of these particular paths must omit at least eleven original sites. A 192-edge snake without the single-interval restriction must omit at least three. These are statements about the listed 191-edge shapes. [Two-site continuation from 191](growth-from-191.json) · [All consecutive-omission cases](interval-growth-191.json)

## Exact capacity of a 90-edge forbidden segment

Translate the original crossing to zero. The two 93-edge parents enter opposite ends of the same 90-edge segment, one by $0,1,5,7$ and the other by $0,64,68,70$. The segment has 91 vertices, contains neither root nor intermediate entrance site, and appears in opposite orders in the two arms. **The longest induced eight-dimensional path rooted at zero that avoids just these 91 vertices has exactly 95 edges.**

The common 95-edge donor realises the lower bound. A 96-edge partner avoiding the segment must use some vertex of $\{1,5\}$. Otherwise it would be compatible with the entire first 93-edge parent, contradicting the unrestricted exclusion at 190. It must also use some vertex of $\{64,68\}$ by the second exclusion. Asking for a 96-edge partner with both necessary conditions gives a further independent LRAT contradiction. This excludes every longer partner by deletion at its free end. The stated placement of the segment relative to the crossing is part of the hypothesis. [Ordered segment and entrance paths](shared/transport.json) · [Required-site contradiction and replay](shared/forced-replay-93-96.json) · [Constructive donor](shared/summary.json)

Every occurrence of the segment in another rooted induced path must be a consecutive interval. Matching all such intervals in the 626 earlier rooted arms, with the isometry fixing zero, strengthens two previously unresolved 94-edge crossings to exact maximum 190. Their identifiers begin `11a8a5bdb2` and `8a5b2985dd`. [All coordinate maps, earlier bounds and new ceilings](shared/transport.json)

Among the four selected parent shapes, seven of eight choices of crossing endpoint now exclude 192. The remaining endpoint begins `20c9fd03db` and has verified interval 129–193. Its selected partner search at 192 reached its time allowance. At the two 94-edge crossings initially attaining 189, the exact maximum remains 189 or 190. [Per-root results](summary.json) · [Grouped and split queries](opposite)

## Reproduction and next step

The [guarded execution receipts](runs) give the source hashes and exact arguments. The fixed-arm calculations use `rebuild_saved.py`, `retain_donor.py`, `shared_sites.py`, `forced_hits.py` and `transport_core.py`. The whole-path reconstruction uses `repair_whole.py`, `climb.py` and `repair_intervals.py`. The archive comparison and the literal repair chains use `classify.py` and `chains.py`. Each input from Round 274 is identified by its SHA-256 digest in [the summary](summary.json).

The local next objective is to vary the remaining long arm or permit more than one crossing of the chosen coordinate. The original crossing and the two-site neighbourhood of the recovered 191s have the bounds above. The global nine-dimensional maximum remains open. [Manuscript updates](manuscripts.json)
