# Rebuilding the free arm at a twice-crossed coordinate

**All 49 eligible choices of source path, coordinate and fixed short arm have exact maxima.** These are the nine archived 191-edge charts and 40 archived 190-edge charts whose chosen coordinate is used twice and whose short outer arm has at most three edges. They reduce to 22 distinct fixed middle/short-arm configurations. Each maximum allows the other lower-face arm to vary freely in the entire eight-dimensional face. [Catalogue and source coordinate maps](fixed-short/plan.json) · [Individual bounds and replay](fixed-short/summary.json)

| Exact joined maximum | Distinct fixed configurations | Charts originally of length 190 | Charts originally of length 191 |
| ---: | ---: | ---: | ---: |
| 190 | 17 | 24 | 0 |
| 191 | 5 | 16 | 9 |

The search produced 22 whole-root contradictions at length 192 and 17 at length 191. An independent calculation reconstructed the original projected faces and replayed all 39 certificates. All 16 starting 190-edge snakes in the second row can attain 191 by keeping the full short arm and the entire upper-face middle. The saved 30 ordered replacements across those 16 starts recover nine archived 191-edge shapes. One upgrade keeps the three-edge short arm and 93-edge middle of example 190-428 and substitutes the opposite arm from 191-127, giving 191-127 in the original coordinate frame up to cube symmetry. [All original-coordinate upgrade paths, donors and archive matches](fixed-short/short-donor-upgrades.json)



Write the nine-dimensional path as a lower-face outer arm, a crossing, an upper-face middle $M$, a second crossing, and a lower-face short arm $C$. The middle and both crossing edges retain their positions; $C$ retains every vertex. Place the crossing at the free end of the middle at zero. The free outer arm $B$ begins at zero. Its other endpoint and all its other vertices can change.

An induced $B$ produces an induced nine-dimensional join exactly when it avoids the interior vertices of $M$ and every vertex at distance zero or one from $C$. For vertices in opposite faces, a projected coincidence produces an edge in the nine-cube. This permits precisely the two crossings. Within the lower face a coincidence or a distance-one pair between the two outer arms is forbidden. The original donor already verifies all conditions involving only $M$, $C$, and the two ports. Consequently a target join with $L$ edges is equivalent to a rooted opposite arm of exactly $L-|E(M)|-|E(C)|-2$ edges in the stated domain. Any longer free arm supplies such a prefix. An opposite arm has at most 98 edges.

The source catalogue includes every choice of a twice-used coordinate and a directed short-arm end of length zero through three in the 190- and 191-edge archives. Equal fixed middle and short-arm geometries are grouped after a root-preserving permutation. Every group records its source paths and coordinate maps. A witness is lifted back into each original nine-dimensional chart before its pairwise distance checks.

Use the [guarded runner](../256-two-exchange-parents/run.py) on the following scripts. The exact search selections and time allowances in the published [round receipts](runs) determine which queries were performed.

1. Run `fixed_short278.py plan` to write the full occurrence catalogue.
2. Run `fixed_short278.py search --source-edges 191 --target 192 --seconds 5` for all 191-edge donors with a short arm of at most three edges. To search selected 190-edge donors, use `--source-edges 190` with `--first` and `--count`. Use `--target 191` to try for a constructive improvement to a 190-edge donor. The full arm varies in each query.
3. A later call with `--depth 1` or `--depth 2` divides an open query by its initial steps. `--keys` restricts the call to the given fixed geometries. A verified candidate of length at least 192 is saved in the round-level candidate file, and this search stops.
4. Run `audit_fixed_short278.py`. It re-extracts the coordinates and directions directly from the full archived sequences, reconstructs the forbidden sites from Hamming distances, rebuilds every queried formula and verifies each exclusion certificate. It checks coverage of all legal next steps and every ordered positive path in the original nine-cube. The resulting endpoint bounds and witness archive matches are in [the replay](fixed-short/summary.json) and [positive paths](fixed-short/positive-paths.json).

A time-limited query yields no upper bound. Results apply to a retained middle, its specified crossing ports, and the specified retained short arm.
