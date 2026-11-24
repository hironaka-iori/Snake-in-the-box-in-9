# Round 266 · Rebuilding the opposite arm

**Holding either whole arm at its published crossing gives an exact maximum of 191 edges for all 25 archived one-crossing 191-edge snakes.** Each example splits into arms of lengths 94 and 96. Round 248 classified the partners of the longer arm. This round fixes the shorter arm and searches the whole opposite face. A partner of 97 edges would attain 192. [Rooted census and certificate replay](summary.json) · [Earlier long-arm census](../248-rooted-arm-capacity/README.md)

## Results for the five shorter-arm shapes

| Fixed crossing endpoint | What the unrestricted partner search established |
|---|---|
| Published end of each 94-edge arm | The maximum partner length is 96. Each labelled arm has precisely five attaining partners. Their 25 joins are the published examples. |
| Opposite end of each 94-edge arm | Every partner has at most 93 edges, so the join has at most 188. The five best explicit joins from placement and regrowth have lengths 172, 178, 178, 182 and 183. |

The opposite endpoints illustrate how much the crossing location matters even for the same arm. The longest constructed example at an opposite endpoint has 183 edges. Its donor placement initially gave 143. All five reverse-end constructions were checked in vertex order. Whole-root searches at joined length 186 hit their time limit at all five roots. The attainable lengths and the ceiling of 188 leave gaps. [Ordered constructions](constructed.json) · [95-edge partner exclusions](partner-190.json) · [94-edge partner exclusions](partner-189.json) · [Unresolved 186-edge queries](partner-186.json)

## Why the census is complete

Translate the fixed crossing endpoint to zero in both eight-dimensional faces. In the opposite face, any induced path from zero avoiding the nonzero sites of the fixed arm forms a valid join. An additional intersection of the projected vertex sets would give a chord. For a partner of $n$ edges, choose exactly $\lfloor n/2\rfloor+1$ even vertices and $\lceil n/2\rceil$ odd vertices. Require zero and exactly one other endpoint, of parity $n\bmod 2$, to have induced degree one. Each remaining selected vertex has induced degree two. The component containing zero is the required path if all selected vertices belong to it. Each other component is a cycle and its complete vertex set is forbidden in every induced path.

The first enumeration excluded a 97-edge partner at all ten endpoints. For the second, each known 96-edge partner was verified and its vertex set individually forbidden. A fixed starting point determines the traversal of an induced path. The second enumeration then closed all ten cases. For each exclusion the verifier regenerated the formula, checked the validity of its cycle exclusions and replayed the contradiction certificate. Any longer partner contains a prefix of the queried length. [Unrestricted 97-edge queries](partner-192.json) · [Complete 96-edge census after removing the known partners](partner-191-census.json) · [Formula and search](rebuild.py) · [Replay program](verify.py) · [Proof files](proofs/)

## Changing the fixed parent for a later search

All possible ways to extend one of the five 94-edge parents at either tip in its own face give exactly eleven shapes of length 95 and two of length 96, up to cube isometry and reversal. None reaches 97. Any occurrence of one of the five as a consecutive interval in a longer arm can be reduced back to it by removing tips. This proves completeness of the extension procedure. An independent traversal that first extended one side and then the other returned the same 18 shapes including the five starts. The two-ended enumeration here concerns only the eight-dimensional parent. The opposite arm is still the sole arm changed in each nine-dimensional reconstruction. [All parent shapes and extensions](windows.json) · [Independent traversal](verify.py)

If a 95-edge arm begins at the crossing with an intact 94-edge reference, checking whether it can join to 192 is especially simple. Any 96-edge partner would also fit the 94-edge prefix. At the reverse endpoint there is no such partner. At a published endpoint there are exactly five. For all 25 labelled attaining pairs, adding a legal edge to the free end of the fixed 94-edge arm would cause an extra projected intersection with the partner. The verifier checked this directly. The enumeration of eight-dimensional shapes also includes placements with the added edge at the crossing.

## Construction sources and scope

The 398 archived arm pairs from Round 265 gave the fixed arms and their known partners. To obtain additional lower bounds, 61,514 normalized directed donor words from 1,157 eight-dimensional shapes were placed under all coordinate permutations. The opposite arm alone was then regrown. The five published-end parent masks can be aligned to share 85 blocked vertices, and the five reverse-end masks to share 60. Those intersection sizes describe the saved placements. The impossibility certificates use the full fixed parents. [Input catalogue](parents.json) · [Donor search](construct.py) · [Coordinate alignments](aligned.json) · [Source pairs](../265-joint-arm-regrowth/exchange.json)

The global interval is $191\le a(9)\le230$. The contributor branch was checked at revision `3e156b298f`. Its saved audit passed. A fresh independent full rebuild of the contributor theorem remains pending. [Contributor evidence](../264-distant-component/contributor.json) · [Manuscript receipts](manuscripts.json) · [Guarded execution records](runs/)
