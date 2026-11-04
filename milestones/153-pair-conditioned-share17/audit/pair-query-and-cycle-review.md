# Conditional share-17 query and saved critical cycles

The proposed restriction has no direct effect on either saved critical cycle. The eleven-cycle has four canonical `012032` windows, all with exact second-plus-fourth count equal to nine. The fourteen-cycle has no `012032` window. This supports deprioritizing the restricted query after its bounded timeout. It does not exclude a possible reduction of the potential range on other rows.

## Query verification

The input tests the conditional statement that a fitting `012032` window with actual pair count at least ten has five-centre share at least 17. Its contradictory input has share cap 16 at resolution 12, five broad count bounds `[0,21]`, radius four, and the ordinary endpoint budget two. It assumes the pair restriction; it does not establish that restriction for arbitrary snakes.

The 94,331-clause prefix is byte-identical, apart from the DIMACS header, to milestone 152's universal cap-16 input. Independently reconstructing the added counter reproduced all 508 appended clauses and all 174 fresh variables, giving 94,839 clauses and 11,825 variables. The counter preserves all 42 missing-corner occurrences over 37 distinct vertices. Its downward clauses and positive tenth-output unit enforce at least ten true input occurrences. There are no appended cycle exclusions.

The attempt ended with `TIMEOUT` after 92.453 seconds under a 90-second limit. The saved partial trace is 100,036,608 bytes. No complete replay record exists. The local share-17 statement remains unresolved.

## Indexing and the eleven-cycle

Each row stores nine transitions and six count symbols for chronological vertex positions 3 through 8. The suffix window uses transitions `directions[3:9]`; its five internal counts are `counts[1:6]`. Consequently its second and fourth internal counts are `counts[2]` and `counts[4]`. Reversal exchanges those two counts and preserves their sum.

The relevant suffix rows are:

| Cycle position | Edge | Six stored counts | Second and fourth internal counts | Sum |
|---:|---:|---|---|---:|
| 0 | 2222339 | 5, 4, 4, 4, 5, 3 | 4, 5 | 9 |
| 2 | 2221095 | 4, 4, 5, 3, 4, 4 | 5, 4 | 9 |
| 7 | 2534 | 4, 4, 4, 3, 5, 4 | 4, 5 | 9 |
| 9 | 2220859 | 4, 3, 5, 4, 4, 4 | 5, 4 | 9 |

All these symbols are below six and therefore exact. The four eligible prefix matches, on the following rows, describe the same occurrences. They must not be counted again. Checking all four possible six-transition placements in each nine-transition row gives sixteen representations of the same four periodic occurrences, all with exact pair sum nine. Closed adjacency, direction overlaps, and count shifts were independently checked from the saved rows.

In general, a stored six means an actual count in `[6,21]`. A clipped pair sum of at least ten certifies the query's premise. A smaller clipped sum containing six can be ambiguous. That ambiguity does not arise in this eleven-cycle.

## Fourteen-cycle

The fourteen-cycle has eight suffixes of shape `012304`, four of shape `012301`, and two of shape `012340`. It has no `012032` suffix in either orientation. The check of all four placements likewise found none. Thus any increment confined to `012032` with actual pair at least ten leaves every weight on this cycle unchanged.

## Weight profiles and mathematical scope

The same eleven-cycle has different weights in the preserved profiles. Its milestone-144 total is 5399. Under milestone 149's fixed floors and universal `012032` floor 15, its total before occurrence credit is 5452; credit one adds four, producing 5456. Installing a universal `012032` floor 16 also raises that profile's total before occurrence credit to 5456. The proposed pair-at-least-ten increment adds zero in each case.

The milestone-145 fourteen-cycle expression remains

\[
6848+4F+2G,
\]

where \(F\) and \(G\) are its `012301` and `012340` floors. Its first two edges still have total \(496+F\). For that preserved weight model, the old two-cycle arithmetic and its hypotheses remain unchanged by the restricted increment. In particular, its recorded \(F=G=16\) comparison lower bound is \(551875/2348=235+95/2348\).

That numerical obstruction uses its original `012032` baseline. It cannot be transferred unchanged to a profile that also installs the newly proved universal share-16 floor. Milestone 149 also uses an older graph; some of its other obstruction rows are absent from the later milestone-144 graph. The eleven-cycle itself survives that removal set.

These are cycles in a finite graph relaxation. They are not asserted to be actual snakes. Their invariance neither disproves the proposed conditional local theorem nor establishes a global snake bound. It also leaves open a range improvement caused by increasing weights elsewhere. A further attempt on this restricted query should therefore require evidence of such a benefit, rather than an expectation that it changes these cycles.

## Audit scope

The accompanying JSON records exact source and saved-evidence hashes, all cycle rows and matches, the input reconstruction, and terminal native status. Original source-array extraction is inherited from the pinned independent milestone-144 and milestone-149 audits. This review independently recomputed saved count decoding, canonical words and reversals, all four placements, adjacency, count shifts, and the stated arithmetic. It did not reload the full graph or repeat an optimizer, solver, Lean check, or proof replay. Running proof jobs and all files outside the two assigned audit outputs were left untouched.

## Addendum: exact critical context

The separate `critical` query uses the correct indexing. Edge 2222339 has stored counts `[5,4,4,4,5,3]`; the suffix's five internal counts are `[4,4,4,5,3]`. Its forward suffix already canonizes to `012032`, so no reversal of these bounds is required. The second and fourth internal counts are four and five, giving exact pair nine. The query has share cap 16 and target 17, with these exact five bounds and no pair-at-least-ten assumption. Its preparation records 13,856 variables and 98,836 clauses.

This context directly matches edge 2222339. After a valid reversal transfer, it also matches edge 2220859, whose five chronological counts are `[3,5,4,4,4]`. Therefore, if the local share-17 result and both orientation transfers are established, it would increase these two row weights by one each relative to the same milestone-149 profile with universal `012032` floor 16. The eleven-cycle total would rise from 5456 to 5458 before occurrence credit. This is a conditional saved-row calculation; other critical cycles and the full potential remain separate.

The addendum verifies preparation, indexing, and saved source hashes only. The query's observed status is captured in the accompanying JSON. Its proof output has not been audited, and no local theorem is claimed from this addendum.
