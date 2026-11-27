# Round 276. Opposite partners of an optimal eight-dimensional arm

The 98-edge Carlson snake has exactly one other labelled optimum within eight vertex replacements in $Q_8$. This nearest optimum replaces seven vertices and is isometric to the original. In $Q_9$, keeping the whole Carlson arm and choosing either end as the crossing gives a verified 180-edge snake. The maximum in each of those two families lies between 180 and 187 edges. A 192-edge construction along the single-crossing route therefore requires a different fixed arm.

## The nearest optimum in eight dimensions

Write $S$ for the 99 occupied vertices of the Carlson path and $T$ for the 99 vertices of any other 98-edge snake, in the same coordinates. Define the replacement distance by $d(S,T)=|S\setminus T|$. A path and its reversal give one occupied set.

| Replacement distance | Number of distinct occupied sets at that distance |
|---|---:|
| 0 | 1 |
| 1 through 6 | 0 at every distance |
| 7 | 1 |
| 8 | 0 |

The unique set at distance seven removes $21,78,80,82,153,212,223$ and adds $16,86,93,157,159,199,216$. Its endpoints are $137$ and $199$. To construct it, interchange coordinate bits 2 and 6 (numbering from zero) and then translate by bitwise XOR with $137$. Consequently, every inequivalent 98-edge snake would require at least nine replacements from this labelled set. The existence of an inequivalent optimum remains open in this investigation. The bounded attempts at radii 9 and 10 ended open.

All $10{,}321{,}920$ cube isometries produce distinct images of $S$. Exactly one produces the distance-seven image. The unconstrained occupancy proof separately covers every induced 98-edge path at each of the eight certified distances. [Literal nearest path and isometry](isometry-orbit.json) · [Exact sphere results](site-distance.json) · [Certificate replay](site-distance-replay.json)

## The two fixed crossings in nine dimensions

At each crossing the fixed 98-edge arm, one crossing edge and a constructed 81-edge opposite arm give 180 edges. All 16,290 unordered pairs of vertices were checked in each joined path. The two witnesses are inequivalent under reversal and cube isometry. Neither occurs as a consecutive window in the archived 190- and 191-edge paths scanned by Round 265.

| Raw endpoint of the fixed arm | Earlier bounds | Current bounds | Prefixes still open at target 187, after translating the crossing to zero |
|---|---|---|---|
| 0 | 179–187 | 180–187 | $(0,4)$, $(0,32)$, $(0,64)$, $(0,128)$ |
| 78 | 179–187 | 180–187 | $(0,32,40)$, $(0,32,48)$, $(0,128,136)$, $(0,128,192)$ |

For endpoint 0 the new contradictions exclude first moves to $2,8,16$. For endpoint 78 they exclude the first move to $64$ and the prefix $(0,128,144)$. The common upper bound of 187 was already certified in Round 249. The fixed-crossing results concern the specified 98-edge shape. [Explicit 180-edge path](best-join.json) · [Both witnesses and remaining cases](endpoint-results.json) · [Round 249 audit](../249-long-parent-joins/audit98.json)

## Other long parents considered

The primary records of Carlson, Rokicki and the independent Snakepits annealer represent the same 98-edge shape. They were compared in vertex coordinates. The earlier archive supplied 25 inequivalent 97-edge shapes and this one 98-edge shape. Across all 26 seeds, rebuilding an internal interval of at most 17 omitted sites and up to seven free-end sites gave 598,272 choices of retained blocks. Two traversal orders recovered exactly the same outputs. Six seeds attained 98 edges, with one labelled output per attaining seed, all isometric to Carlson. These results suggest looking outside this neighbourhood for a 98-edge parent that could accept a 93-edge partner. [Input reconciliation and sources](input-arms.json) · [Full reconstruction](anchors-all-g17-e7.json) · [Method and proof details](METHOD.md)

## Reproduction

Run the scripts from the repository root through the existing resource guard. The first command rebuilds and checks the eight sphere contradictions. The second checks the five new opposite-arm contradictions and both geometric witnesses. The third reconciles them with the explicit nearest image and archived constructions.

```powershell
python -B milestones/256-two-exchange-parents/run.py milestones/276-partners-of-optimal-arms/sphere.py replay
python -B milestones/256-two-exchange-parents/run.py milestones/276-partners-of-optimal-arms/partners.py audit
python -B milestones/256-two-exchange-parents/run.py milestones/276-partners-of-optimal-arms/signature.py
```
