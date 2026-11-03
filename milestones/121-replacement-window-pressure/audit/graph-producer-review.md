# Milestone 121: pair-restriction graph computation

The single graph recomputation completed successfully. The three pair interval
exclusions remove 14,646 additional transitions beyond milestone 120. They break
its conditional five-cycle at edges 2511 and 1101529. A replacement four-cycle
preserves the same mean and potential range. Neither integer comparison improves.

| Profile | Mean | Potential range | Exact comparison | Integer comparison |
| --- | ---: | ---: | ---: | ---: |
| Completed-share profile | $2915/6$ | $1730/3$ | $1324108/5623$ | $235$ |
| Conditional-share profile | $496$ | $602$ | $551765/2348$ | $234$ |

Both experiments retain the inherited thirteen sum-rule hypotheses and their
outstanding global assembly obligations. The profile names identify the share
catalogues. These calculations establish no new actual-snake upper bound.

## Restrictions and reproduction

The computation first reproduces the full milestone-120 removal set and both
complete retained weight-vector hashes. It also preserves the predecessor
checks against milestones 117 and 119. The milestone-120 outer-count restriction
is retained without alteration. All inherited weights, their maximum-deficit
combination and the shared coefficient budget are unchanged.

The new canonical direction pattern is $012032$. Its three excluded intervals
are

$$
([0,21],[0,1],[0,21],[0,21],[0,21]),
$$

$$
([0,21],[0,2],[0,21],[0,5],[0,21]),
$$

$$
([0,21],[0,3],[0,21],[0,4],[0,21]).
$$

Each is applied at both five-count placements in every nine-transition key,
and in both orientations. Reversal cannot be skipped simply because the
direction word canonicalizes to itself: the interval caps are asymmetric.
For symbol 6, containment uses its full interval $[6,21]$.

The first restriction removes no keys from the source graph. The second hits
8,857 keys, and the third hits 9,281 keys, of which 5,789 are additional after
the second. Their union removes 14,646 keys beyond milestone 120. The total
removed set has 263,894 keys, leaving 4,683,114 edges on 1,601,856 states.

As a separate full-mask check, the union of the explicit interval hits agrees
exactly with rejecting $a<2$, $b<2$ or $a+b<8$, where $a,b$ are the second and
fourth clipped counts in a matching five-count window. No additional excess
credit is assigned by these restrictions. Their actual-snake proof status is
recorded separately by the proof receipts; the native probe labels remain
unchanged in their original evidence.

## Surviving cycles

The completed-profile eighteen-cycle from milestone 120 survives unchanged.
Its full keys are recorded in the results. The new conditional cycle is:

| Edge | Nine directions | Six count symbols | Weight |
| ---: | --- | --- | ---: |
| 2222588 | $012314354$ | $(5,5,3,3,5,5)$ | 616 |
| 148850 | $012032435$ | $(5,3,3,5,5,3)$ | 376 |
| 2219941 | $012314354$ | $(3,3,5,5,3,3)$ | 376 |
| 146842 | $012032435$ | $(3,5,5,3,3,5)$ | 616 |

All four history values are zero, and all four added sum-rule bonuses are zero.
The weights sum to 1,984. The distinct five-count windows are $012314$ with
$(5,5,3,3,5)$ or $(3,3,5,5,3)$, and $012032$ with $(5,3,3,5,5)$ or
$(3,5,5,3,3)$. The latter two have second-plus-fourth count exactly 8. Thus the
new pair inequality alone cannot remove this cycle. These are graph contexts;
no actual snake realizing them has been established here.

## Verification and evidence

The producer checked every retained-edge potential inequality for each profile
and saved an attaining cycle. A subsequent calculation rechecked source pins,
cycle chaining, count-code reconstruction, exact mean, decompressed potential
hash and range, equality on every saved cycle edge, and comparison arithmetic.
That second calculation is saved in `data/pair-graph/cycle-review.json`.

This is a producer computation and saved-data check. It does not constitute an
independent reconstruction of all graph data or a Lean proof. No SAT solver or Lean
compiler was launched by this worker. The active proof jobs and their inputs
were left unchanged.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_pair.py` | `dc4c28743da89797a59966548dc0c4a384ad3bba300ffa520c9dd5030e80c514` |
| `data/pair-graph/results.json` | `7492ff3a45178740d3253c679bcdd2f5e7907be907f055f455e739cde0b327bf` |
| `data/pair-graph/cycle-review.json` | `886b19e36e1eb7be639eafdd08386a8ebc7d989f8b0f2009092357b6acb01dc2` |

The script refuses to overwrite an existing results file. This report covers
one completed recomputation only. No second coefficient optimization was run.
