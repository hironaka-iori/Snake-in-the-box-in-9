# Independent review of the middle-count total-sum experiment

This bounded audit checked the saved cycles, exact graph keys, diagram membership, state endpoints, base weights, all ten rule deficits at both placements, potential bytes and ranges, removal-set arithmetic, and rational comparisons. It did not rerun a solver, Lean compiler, graph optimization, all-edge rule evaluation, or all-edge potential test. The reusable audit script completed successfully in approximately four seconds. A Git commit-graph warning did not prevent retrieval and hash verification of the pinned algorithm source.

## Results and evidence scope

| Profile | Cycle length | Exact mean | Potential range | Comparison | Integer part |
|---|---:|---:|---:|---:|---:|
| Completed local floors | 7 | $3396/7$ | $4089/7$ | $2574659/10932$ | 235 |
| Conditional floor18 | 19 | $496$ | $602$ | $551765/2348$ | 234 |

The word “completed” names the existing local-floor profile. Both new experiments assume the ten-rule family, including unproved sum restrictions. These are native finite-graph results; no new actual-snake upper bound is established.

Every saved edge was matched to the pinned original graph by its direction, history, six-count code and raw endpoint indices. Direction literals, diagram nodes, class roots and block assignments were matched to their Lean source literals. Each cycle closes, is accepted by the full-key diagram, survives the saved removal set, and has the reconstructed original weight with the appropriate profile floor. The completed cycle's weights are $612,360,480,492,480,372,600$, summing to 3396. The conditional cycle has total weight 9424 across 19 edges.

Both compressed potential files were decompressed and their uncompressed hashes verified against the result. Each contains 1,601,856 signed 64-bit entries, has minimum zero, and has maximum 4089 or 602 as appropriate. Every saved cycle edge has zero slack in

$$
p+\pi(v)\le d\,w(u,v)+\pi(u).
$$

The comparisons were independently recomputed as

$$
\frac{1098960d+8p+R}{4200d+p}.
$$

The producer's all-edge inequality assertion and whole restricted-weight hash were inspected and pinned, but were not independently recomputed over every edge. Thus this audit independently verifies the cycle upper ceilings and saved potential range, while relying on the producer for the matching all-edge lower certificates.

## Rule alignment and interval treatment

For the nine-transition extension $d_0,\ldots,d_8$ and six symbols $c_0,\ldots,c_5$, the placements are $d_{s+2},\ldots,d_{s+7}$ paired with $c_s,\ldots,c_{s+4}$, where $s=0,1$. The evaluator tests both placements for deletion and awards excess credit only at $s=1$. Credit from alternative rules is combined by a maximum.

Each count symbol below 6 is exact; symbol 6 denotes the entire interval $[6,21]$. A cap condition is used only when it contains the whole represented interval. A positive sum deficit causes deletion only when all selected symbols are below 6. Otherwise its weighted deficit may supply excess credit. All ten rules have reversal-symmetric bounds and selected positions, which justifies using the minimum of the forward and reversed canonical shapes without separately reversing the condition. The new $012345$ rule has a middle cap of 3 and a total lower bound of 22, so this symmetry holds.

For every saved cycle edge, all ten applicable deficits are zero at both placements. This directly verifies both deletion survival and the recorded zero bonus; it is stronger than merely reading the bonus field.

## Fixed-family coefficient ceiling

The saved cycles survive all coefficient-independent deletions and have zero deficit for every rule. Their edge weights remain unchanged for every nonnegative choice of deficit coefficients within this fixed family. Summing any potential inequality around these cycles yields mean ceilings $3396/7$ and $496$. Balanced coefficients 24 attain those means according to the pinned all-edge computations. Further coefficient search within this unchanged family cannot improve either mean beyond these ceilings.

Even a potential range of zero would not exclude the next desired integer through the current comparison. At the mean ceilings,

$$
1098960\cdot7+8\cdot3396-(4200\cdot7+3396)\cdot235=12828>0,
$$

and

$$
1098960+8\cdot496-(4200+496)\cdot234=4064>0.
$$

A stronger rule or a changed argument is required for that improvement through this comparison. This is an arithmetic consequence for the current graph, rather than a limitation on snakes themselves.

## Removal counts and native probes

The saved removal set contains 111,297 distinct original edge indices, leaving 4,835,711 of the original 4,947,008. Its inclusion relations and counts were verified: 106,878 removals beyond the fixed milestone111 baseline, 32,155 beyond milestone113's eight-rule family, and 29,892 beyond milestone114's nine-rule total19 experiment. The last number equals the new rule's marginal count. This audit checked the stored sets and arithmetic without reevaluating every deletion predicate.

All four new probe records are `UNSAT_UNCERTIFIED` with zero added cycle cuts. Their definitions and source pins match the saved experiment:

| Probe | Recorded native seconds |
|---|---:|
| Exact $[4,3,3,5,4]$ | 0.625 |
| Exact $[5,4,2,5,5]$ | 0.406 |
| Exact $[5,4,3,4,5]$ | 5.766 |
| Middle count at most 3, total at most 21 | 9.734 |

The fourth probe motivates the new total lower bound; the three exact probes are narrower supporting tests. None of these records supplies a checked refutation. Their status is independent of the separate Lean certificate work for $012310$.

## Common next cell

The only common suffix shape of the replacement cycles is $012345$. A completed-cycle window at edge 3374668 has counts $[3,4,4,4,3]$, of total 18. It also occurs at the earlier placement of edge 1776323. A conditional-cycle window at edge 2977981 has symbols $[3,4,4,6,3]$, of clipped total 20; it also occurs at the earlier placement of edge 1008309. The new rule misses both because their middle count is 4.

One common bounded test is $012345$ with first and fifth counts at most 3, middle count at most 4, and total at most 20. If a checked contradiction established total at least 21 under those caps, it would exclude the exact completed cell. In the conditional cell, symbol 6 permits larger actual counts: the result would force at least one unit of excess and could supply credit rather than unconditional deletion. This test is unperformed and no local inequality is asserted here. Other conditional $012345$ windows contain symbol6 and must retain their interval interpretation.

## Pins and reproducibility

Paths are relative to `milestones/115-total-count-certificate`. The JSON includes inherited source pins, exact decoded cycle windows, membership routes, both-placement rule tests and probe records. The script prints by default and uses exclusive creation with `--output`; it will not overwrite the saved audit.

| File | SHA256 |
|---|---|
| `scripts/independent_cycles.py` | `278823de20108883a394f2dfcf2af70634345eb9a999e1ecd3fde188f2ad0471` |
| `data/graph-cycle-audit.json` | `a9b83e3300674dce27dfb3c61b9a5d57e89ee7b862cc64cd3dec4b1151807c92` |
| `scripts/evaluate_total.py` | `fcdb27ab4f9df5919aa3903216d1384244a309eac56002a43d703199b78dc3d0` |
| `data/middle345-total22/results.json` | `1285e723de63bad74a7b973003720f3cbc0ec60d19ae3fecb76a7449d750ba66` |

Verified uncompressed potential hashes: completed `ab5ec5b15d245bd035ee08f79175c5b5af3e07662be7cde1a11171b95ab31bc0`; conditional `e841007f8d6de124cb02384e012b75883dc0742a2cbf93ec13d943ded179b8e5`. The audit JSON also pins their compressed files.
