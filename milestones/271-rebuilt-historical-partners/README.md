# Round 271. Rebuilding the opposite arm of 54 long eight-dimensional snakes

**All 108 fixed crossing endpoints exclude a 192-edge join.** The same ceiling of 191 applies when any of the 54 parent shapes occurs as a consecutive interval anywhere in either arm of a nine-dimensional snake with a once-crossed coordinate. Two of the fixed endpoints have **exact maximum 189**. [All endpoint bounds](summary.json) · [All interval bounds](intervals.json) · [Reported results in the two manuscripts](manuscripts.json)

## Two different 189-edge snakes

The same 92-edge opposite arm fits two inequivalent 96-edge parents after a coordinate permutation. The joined paths have $96+1+92=189$ edges. Each of these two crossings had a 133-edge construction in Round 270. An unrestricted search excluded every 93-edge opposite arm at both crossings, establishing the exact maxima. The original-coordinate witnesses each satisfy all 17,955 pairwise distance checks. Neither admits an extension at either end, and neither occurs as a contiguous interval of the 1,042 archived 190-edge snakes or the 131 bank 191-edge snakes. [Both paths and their symmetry comparison](long-joins.json) · [One complete path](best-join.json) · [Exclusion at 190](queries-190.json)

Placing the 92-edge donor at all 108 endpoints, in both directions and under all $8!$ coordinate permutations, gives 8,709,120 placements. The only complete fits are the two above. [Exact placement counts](new-donor.json)

## What the exclusions cover

The parent collection consists of 36 shapes of length 96 and 18 of length 97, each with two choices of crossing endpoint. Every induced opposite arm was allowed. The upper bounds and the number of endpoints receiving each are as follows. [Search, certificate replay and free-tail results](UNRESTRICTED.md)

| Verified ceiling in joined edges | Fixed endpoints | Endpoints with a verified construction at the ceiling |
| ---: | ---: | ---: |
| 188 | 15 | 0 |
| 189 | 2 | 2 |
| 191 | 91 | 0 |

To handle a parent appearing strictly inside an arm, every legal single-edge extension at both ends was generated. All 17 resulting parent-to-child shape relations stay within the original collection. Following these relations gives an interval ceiling of 191 for 53 shapes and 188 for one. The conclusion applies specifically to one-crossing snakes containing one of these named shapes. The general nine-dimensional maximum remains open. [Extension graph, attaining lower bounds and interval ceilings](intervals.json)

## Two other ways to reach 188

Keeping the 97-edge arm of Casella’s 186-edge example gives a 90-edge partner and a join of 188. This is the exact maximum at that crossing if both arms also cross the specified internal coordinate exactly once. Keeping the 96-edge parent of Round 270’s 187-edge construction gives a second, inequivalent 188. Reaching 188 at that crossing requires omitting at least nine sites of the former partner, and the construction attains nine. [Both constructions and their restricted proofs](CONSTRUCTIONS.md)
