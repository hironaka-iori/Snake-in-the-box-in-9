# Round 274 · How many sites of a long arm can be kept?

**The five shorter arms from the 25 archived one-crossing 191-edge snakes give exactly 297 replacement shapes of length at least 93 when at most two original vertices are omitted. Their maximum length is 96.** A separate 92-edge arm, shared by two 189-edge constructions, cannot gain even one edge after any three omissions. These conclusions allow new endpoints, a new crossing, arbitrary order of the retained pieces, and arbitrary additions subject to inducedness. [Enumeration and completeness argument](METHOD.md) · [Verified results by source](results.json)

## Replacing an eight-dimensional arm

All lengths count edges. Translation, coordinate permutation and path reversal identify equivalent eight-dimensional shapes. For a 192-edge one-crossing join each arm must have at least 93 edges.

| Starting arm or family | Allowed omissions | Shapes of 93 or more edges | Rooted cases excluding 192 | Largest verified join | Verified upper bound for this family |
|---|---:|---:|---:|---:|---:|
| All five 94-edge arms from the archived 191s | 1 | 118 | 141 of 236 | 191 | 193 |
| Same five arms | 2 | 297 | 177 of 594 | 191 | 193 |
| 97-edge arm from the additional Round 273 join | 2 | 16 | 26 of 32 | 189 | 193 |
| Common 92-edge arm from Round 271 | 3 | 0 | No eligible roots | 189 | 191 |

The 297 shapes in the five-arm family break down as 91, 148, 53 and five at lengths 93, 94, 95 and 96. Both enumerations agree on all 961 labelled paths across the five source neighbourhoods. The 97-edge seed adds 16 further shapes. Together the nonempty families have 313 distinct shapes and 626 directed crossing endpoints. [Source coordinates](selected-start.json) · [Canonical shapes and every source membership](union-paths.json) · [Source-specific certificate coverage](union274/slices.json)

For the common 92-edge arm, every one of the 134,138 choices of up to three omitted vertices was examined. If the omissions form at most two intervals along the seed, the search also rules out all 394,576 choices with four to 16 omitted vertices. A 192-edge join using an arm derived from this seed must therefore omit at least four of its vertices. If its omissions lie in at most two intervals, it must omit at least 17. [Arbitrary omissions and replay](common92-catalogue-replay.json) · [Two-interval replay](common92-two-run-replay.json)

## Nine-dimensional constructions and bounds

The placement search used 3,865 donor shapes and 58,405 directed donor segments, with all eight-axis permutations available at each crossing. Nine rooted parents admit a 191-edge join. The verified paths represent eight shapes, all present among the 131 archived 191s. None of those eight paths extends at either tip. [Complete ordered 191-edge paths and archive matches](record-joins.json) · [Every best donor placement](union-placements.json)

With the opposite face unrestricted, the combined evidence excludes 192 at 203 of the 626 rooted cases. Direct searches in this round exclude it at 93 roots. Earlier certified results apply at 125, with 15 roots in both counts. Across these reconstructed families the verified upper bound is 193. The remaining 423 roots are open at 192. A search that ended at its time allowance contributes no exclusion. The run ledger records batches interrupted at the saved memory reserve. [Interrupted batches](resource-stops.json) [Per-root lower bounds, ceilings and proof status](union274/summary.json) · [Earlier bounds with vertex-by-vertex isometries](union274/inherited.json) · [152 compressed contradiction certificates](union274/proofs)

Casella’s published 97-edge arm has an exact maximum of 188 at its original crossing with all opposite arms allowed. The 97-edge arm of the other Round 273 construction has verified lower and upper bounds of 188 and 188. [Shortening proof for the two roots](HISTORICAL-188.md)

Deleting the original crossing vertex from the second 97-edge arm moves the crossing to its next vertex. The unchanged 96-edge suffix then accepts a 92-edge partner, improving the join from 188 to 189. This recovers a Round 271 path. Both crossing positions have exact maxima for their respective fixed arms. [The move in original coordinates](crossing-one-step-inward.json)

At target 194 the final 95-edge parent would need a 98-edge opposite arm. After the last unresolved prefix, the only legal next vertex gives the four-vertex projected sequence 41, 9, 13, 5 in the representative cube coordinates. The search at that prefix has a contradiction certificate. [Final group and prefix records](union274/queries-194/sub-1c79e193cf73491266b8.json)

## Evidence and reproduction

The [guarded runner](../256-two-exchange-parents/run.py) applies the project's saved resource limits. Each [run receipt](runs) records the actual arguments and source digest. The computations can be reproduced in the following order.

1. Use `starts.py` to extract the five 94-edge arms and the selected 97-edge arm. Run `near.py` with at most three omissions for `common92` and two for each other source. Run `check_catalogue.py` on each source. For the two-interval calculation run `near_tip.py` for each removal count from four through 16, followed by `check_runs.py`.
2. Run `union274.py build`, `face274.py plan --source union` and `place.py --source union --top 32 --iterations 6500`. Run `record_joins.py` for the nine record-attaining placements. The union identifies identical normalised rooted arms across source seeds.
3. Reproduce the grouped search and its refinements from the recorded `face274.py` arguments. The audit reconstructs the permitted sites and Boolean clauses, checks each proof, and verifies positive witnesses in the original cube coordinates. Run `union274.py slice`, `profile.py` for each source, and `combine.py` for the source and family summaries. [All groups and coordinate maps](union274/plan.json) · [Compiled manuscripts](manuscripts.json)

The project remains at a verified lower bound of 191 and the contributor’s upper bound of 230. A fresh independent full rebuild of the contributor’s proof remains pending. [Contributor theorem and audit](../272-forty-nine-edge-parents/contributor.json)
