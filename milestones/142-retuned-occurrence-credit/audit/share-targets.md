# Share-floor targets on the zero-event nine-cycle

Status: **PASS_SAVED_ROW_SHARE_TARGET_AUDIT**. Exactly one added count-free floor affects this cycle: the conditional floor 18 for `012034`. Its six affected rows gain 66 in total. The other four added floors have no matching rows.

The selected next test is the weaker count-free claim that every fitting `012034` window has five-centre empty-square share at resolution 12 at least **13**. This claim remains unproved. It is the smallest integer uniform floor on this shape that removes this cycle's obstruction when occurrence cost and potential range are both zero. The eventual existing conditional-profile requirement remains **18**.

## Exact row comparison

Evaluator lines 296–308 construct the floor tables and take the maximum with the original source weight. All other shared charges on these nine rows are zero. A completed floor 0 means no active count-free floor for that shape in this profile; it does not assert that the actual share is zero.

| Row | Edge | Canonical suffix | Completed floor | Conditional floor | Source weight | Completed weight | Conditional weight | Gain |
|---:|---:|---|---:|---:|---:|---:|---:|---:|
| 0 | 272982 | 012034 | 0 | 18 | 610 | 610 | 618 | 8 |
| 1 | 3726584 | 012034 | 0 | 18 | 489 | 489 | 498 | 9 |
| 2 | 2296749 | 012314 | 16 | 16 | 367 | 376 | 376 | 0 |
| 3 | 265840 | 012034 | 0 | 18 | 730 | 730 | 738 | 8 |
| 4 | 3725533 | 012034 | 0 | 18 | 369 | 369 | 378 | 9 |
| 5 | 2325088 | 012310 | 12 | 12 | 482 | 492 | 492 | 0 |
| 6 | 245838 | 012034 | 0 | 18 | 600 | 600 | 618 | 18 |
| 7 | 3500189 | 012034 | 0 | 18 | 364 | 364 | 378 | 14 |
| 8 | 1647698 | 012314 | 16 | 16 | 366 | 376 | 376 | 0 |
| Total | | | | | | 4406 | 4472 | 66 |

The mean of this cycle changes from $4406/9$ to $4472/9$. The latter is a comparison from the same cycle, not the conditional graph minimum.

## Count clipping and reversal

Rows 1, 4, and 7 have forward canonical suffix `012342`. Reverse their directions and the five-count vector together to obtain canonical `012034`. The affected rows have only three canonical count regimes:

| Canonical count regime | Rows | Interpretation |
|---|---|---|
| `(4,5,3,3,5)` | 0,1 | All counts exact |
| `(3,5,4,3,6)` | 3,7 | Last canonical count lies in $[6,21]$ |
| `(3,6,3,4,5)` | 4,6 | Second canonical count lies in $[6,21]$ |

Symbol 6 must not become an exact-count-six constraint in a local query. The selected count-free claim uses broad bounds $[0,21]$ on all five counts.

Canonical reversal applies to the share claim. The graph term $120c$ always uses the chronological last count. Row 1 has canonical counts `(4,5,3,3,5)`, but its chronological last count is 4; its upgraded weight is $120\cdot4+18=498$.

## One selected next claim

Using the existing share notation, test the following for every fitting actual six-transition window of canonical shape `012034`, including reversal:

$$
\sum_{j=1}^{5}\sigma_{12}(p_{r+j})\ge13.
$$

There are no singleton-count hypotheses. In the existing local-share pipeline, the proposed contradiction query has resolution 12, share cap 12, and five count bounds $[0,21]$. No query or compiler was run here.

The six affected original weights exceed their chronological $120c$ terms by $10,9,10,9,0,4$. Thus an integer floor $h\ge10$ adds $6h-42$ to the cycle total. Floor 12 gives total 4436 and mean $4436/9$, below the zero-cost threshold $111960/227$. Floor 13 gives total 4442 and mean $4442/9$, above that threshold. Since weights increase with the floor, no smaller integer floor removes this specific obstruction.

At floor 13, the zero-credit comparison would require range below $694/9$ if its mean equalled this cycle comparison. Other cycles could have smaller means, and no suitable potential has been found. The selected claim therefore removes only the immediate zero-cost/zero-range obstruction. It does not rescue the existing credit $533/12$ or establish an upper bound.

The historical catalogue already targets the stronger count-free share 20 for this shape, and milestone97 studies floor 18 for an earlier conditional graph. This is a weaker verification task within that existing route. Whether it produces a smaller proof remains untested. Historical floor 17 obstructions are not automatically transferred to the current graph.

## Verification scope

The nine original weight entries were streamed from `weight.npy` in chunks of at most 1 MiB, and the complete member hash was checked against the pinned metadata. The remaining row data agree with the previously audited cycle. The floor tables, reversal, all nine upgraded weights, total gain, and integer floors 0 through 18 were checked directly.

No full graph, solver, Lean invocation, or new agent was used. Existing evidence is unchanged. Exact source pins, canonical count intervals, and arithmetic are in `data/share-targets.json`. The selected local claim is unproved, and no global bound is asserted.
