# Width 34–43 containment review

The exact enumeration transfers 2,053 source exclusions to the 2,625 specified smaller contexts. It leaves 572 contexts uncovered. An uncovered context has no containing width-44 context whose saved status is `STATIC_EXCLUDED` or `INFEASIBLE`; it has not thereby been shown feasible.

| Width | Contexts | Covered | Uncovered |
|---|---:|---:|---:|
| 34 | 231 | 197 | 34 |
| 35 | 238 | 199 | 39 |
| 36 | 245 | 201 | 44 |
| 37 | 252 | 203 | 49 |
| 38 | 259 | 205 | 54 |
| 39 | 266 | 207 | 59 |
| 40 | 273 | 209 | 64 |
| 41 | 280 | 210 | 70 |
| 42 | 287 | 211 | 76 |
| 43 | 294 | 211 | 83 |

## Exact indexing and evidence

Within width $w$, the two closed index intervals are $[a,a+w]$ and $[c,c+w]$, where $0\le a\le6$ and $144-w\le c\le142$. The local ID is $a(w-1)+c-(144-w)$. These IDs are local to each width. The accompanying JSON records every context, all excluded width-44 covers, one chosen cover, and every uncovered ID and interval pair.

The source width-44 IDs are $43A+C-100$, for $0\le A\le6$ and $100\le C\le142$. The combined source contains 107 static exclusions, 102 native infeasibility results and 92 unknown results. The 16 flow reruns are all unknown and add no exclusions. The merge from the two saved result files was reconstructed exactly. No unknown or timeout result was used as an exclusion.

## Why the implication holds

Suppose a smaller candidate exists with equal-length replacements on $[a,b]$ and $[c,d]$, the same original seed outside their open interiors, endpoint 24 appended, and exactly four crossings in coordinate 8. Let $[A,B]$ and $[C,D]$ be containing width-44 intervals. Prefix and suffix each smaller replacement by the unchanged original segments from its containing interval. Each resulting replacement has exactly 44 edges and the larger interval's original anchors. The full concatenated 193-vertex path is unchanged.

Consequently both padded replacements remain induced, have the required alternating colour counts, avoid all forbidden retained vertices and contacts, and have no contact with each other. The two larger intervals are separated by at least 50 index steps, so the model's cross-part prohibition removes no permitted consecutive edge. Original crossing edges added as padding move from the fixed part to the replacement part; their sum still gives exactly four total crossings. The path survives degree peeling and anchor-component restriction. Any induced-cycle occupancy cuts also hold for this path.

Thus any smaller candidate would satisfy the necessary conditions of its larger model. A static exclusion or valid native infeasibility result for that model excludes the smaller candidate. This direction does not require literal inclusion between the two prepared allowed-vertex arrays, whose anchor-dependent definitions can differ. It follows from padding the actual hypothetical path. The reverse implication is unavailable.

## Assumptions and checks

The inspected `prepare_expanded.py` and `joint_regions44.py` impose neither mutual contact with the other old interior nor the earlier short-move closure premise. They retain the stated seed, endpoint, equal-length replacements and four-crossing condition. The optional solver hints are not additional constraints. Hence the inherited exclusions do not depend on the removed mutual-contact or closure assumptions.

This audit independently reconstructed all 301 initial domains, fixed-point degree pruning results, anchor-component restrictions, parity requirements, retained sets, crossing budgets and 107 static reasons. It checked the seed's induced-path geometry and four original crossings. Both execution acceptance records, their source pins, all saved model hashes, terminal infeasibility statuses, and the exact combined merge were checked. Source inspection establishes that the models are necessary relaxations of the stated path family.

The 102 infeasibility claims remain saved native solver evidence. Their solver proofs were not independently replayed, and the containment argument has not been assembled in Lean. No solver, compiler or software test was run. This result does not establish a new snake or a global upper bound.

## Frozen source pins

- `data/combined44.json`: `c4428697e1561f1c5f4e37928827322d59feed70b5df3bbf09dea0808dbbfb4d`
- `data/regions44.json`: `c2c5b1465726c4e8c2ab142a1524e171cfeb992cb66d906475e9d1e2e766ec0b`
- `scripts/prepare_expanded.py`: `19519891b9985a7d907adf307c92b69d1e6760627924beabaa16a953a5b2301a`
- `scripts/joint_regions44.py`: `de09b42cc6dc39c735039606dbce41676b8e86df7e681489f31b910bf0423401`
- `data/pair44.json`: `f1385f1f86fd4ad2d6e4c2ca16160a14d5ff77cba6c9baefac4cbc18d5f10417`
- `data/pair44-execution.json`: `477d3aee31ea8c0c537c2d3cef5f746533465a9dc940014b62b4102946eae9b4`
- `data/pair44-flow.json`: `6019e0b612b0476ae4935a2e2514794c53dbe0ee66a72428897682c23c7e123f`
- `data/pair44-flow-execution.json`: `6f61732c2d225071b8897be70394d651bea7a0a6a1d574a530176e631aa9832d`

All checked source and model hashes are recorded in `data/independent-containment.json`, SHA-256 `ac500a0f1af22828ebc4adeb760fd528deaa3aca4d0b5ba34299e2b765fc645c`.
