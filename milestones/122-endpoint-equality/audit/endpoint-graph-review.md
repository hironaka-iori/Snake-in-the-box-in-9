# Endpoint-credit graph experiment

The selected endpoint credit does not improve either integer comparison in the
current graph family. At coefficient $C=4$, a replacement conditional cycle
avoids every eligible suffix window and retains mean 496. The endpoint-budget
correction then worsens its integer comparison from 234 to 235. Deleting every
eligible suffix also leaves both means and potential ranges unchanged.

## Eligibility and corrected comparisons

Credit is assigned only to suffix five-centre windows with canonical direction
pattern $012032$ whose second and fourth clipped counts are exactly $(3,5)$,
$(4,4)$ or $(5,3)$. All these values are below 6 and therefore specify the actual
counts. The pairs $(2,6)$ and $(6,2)$ are excluded from eligibility. There are
9,577 eligible keys, all retained by the milestone-121 graph.

For the conditional occurrence premise $t\le14$, the comparison used is

$$
m\le\frac{1098960d+14Cd+8p+R}{4200d+p}.
$$

The coefficient schedule was $4,8,16,32,64$. Only $C=4$ was needed: the attaining
conditional cycle then had zero eligible suffixes. The larger coefficients
were skipped after this obstruction was found. No results are claimed for
unexecuted coefficient runs.

| Experiment | Profile | Mean | Potential range | Corrected comparison | Integer comparison |
| --- | --- | ---: | ---: | ---: | ---: |
| $C=4$, budget 14 | Completed-share | $2915/6$ | $1730/3$ | $6620876/28115$ | 235 |
| $C=4$, budget 14 | Conditional-share | $496$ | $602$ | $551793/2348$ | 235 |
| Delete eligible suffixes, budget 0 | Completed-share | $2915/6$ | $1730/3$ | $1324108/5623$ | 235 |
| Delete eligible suffixes, budget 0 | Conditional-share | $496$ | $602$ | $551765/2348$ | 234 |

In the last row, restricting to odd $m$ gives $m\le233$. This parity consequence
already follows from the prior conditional integer comparison 234. It is not
a new bound for all snakes. The odd-case experiment assumes that every eligible
suffix is absent; it does not establish that premise.

## The coefficient-independent obstruction

The new conditional three-cycle has the following full keys. Every history
value is zero; all six count symbols are 4; every weight is 496; every inherited
sum-rule bonus and endpoint credit is zero.

| Edge | Nine directions | Six count symbols |
| ---: | --- | --- |
| 1275804 | $012304235$ | $(4,4,4,4,4,4)$ |
| 3049577 | $012341254$ | $(4,4,4,4,4,4)$ |
| 988624 | $012301430$ | $(4,4,4,4,4,4)$ |

It survives even after all eligible suffixes are deleted. For any $C\ge0$,
adding the nonnegative credit preserves the previous lower potential
inequalities, while this cycle still has mean 496. Hence the conditional
minimum mean is exactly 496 for every nonnegative coefficient in this family.
The completed-profile eighteen-cycle likewise has no eligible suffix and
preserves mean $2915/6$.

Even granting both zero occurrence cost and zero potential range, the best
comparison at these means is

$$
\frac{1323416}{5623}>235
\quad\text{and}\quad
\frac{137866}{587}>234,
$$

respectively. Thus reducing the occurrence allowance or the potential range
cannot improve either current integer comparison while these cycles remain.
This conclusion concerns the specified credit family and retained graph.

The next useful test is an exclusion or additional charge affecting the
displayed all-four cycle. The existing work on six consecutive singleton
counts equal to 4 is a direct place to inspect before starting another search.
Further tuning of $C$ for the current $012032$ endpoint event has no prospect
of improving the integer bounds established by this graph calculation.

## Verification scope

The producer reconstructs the inherited thirteen sum rules, milestone-120 outer
restriction and milestone-121 pair restrictions. It reproduces the entire
milestone-121 removal set and both full weight-vector hashes before adding
endpoint credit. The prior orientations, complete $[6,21]$ bucket intervals,
maximum-deficit credits and coefficient budget are unchanged.

For each of the four reported profile/experiment combinations, every retained
edge satisfies the saved potential inequality and an attaining cycle is saved.
The finite-credit experiments retain 4,683,114 edges. The deletion experiment
removes 9,577 more, leaving 4,673,537. Both use 1,601,856 states. The whole bounded
run took 118.109 seconds after setup of the inherited inputs.

A separate saved-data calculation rechecked source pins, cycle chaining, exact
means, the weight/credit relation, decompressed potential hashes and ranges,
equality on cycle edges, corrected comparisons and the zero-budget,
zero-range limits. It is recorded in `data/endpoint-graph/saved-cycle-audit.json`.
This check does not independently reconstruct the entire graph or rerun all
edge inequalities. No SAT solver or Lean compiler was launched by this worker.

The occurrence premise, the odd-case absence premise, inherited sum hypotheses
and full global assembly have their separate proof obligations. No actual-snake
upper bound is established by this experiment.

| File | SHA256 |
| --- | --- |
| `scripts/evaluate_endpoint.py` | `01325e2b814e1afb3ceb8eef5157d031f4d9ab9656bf06219c0fe4f234f9eee8` |
| `data/endpoint-graph/summary.json` | `f9c5e194a02bd2d165f449e1a326e1d24629d64ccb04c35a743fb783f2bbebe5` |
| `data/endpoint-graph-c4/results.json` | `e57462e65018a9212111f4db1abf149c9725e57fc7523951248e04e14a1c5e6b` |
| `data/endpoint-graph-odd/results.json` | `5858e85db293f7af20490a290c21aac1ec0a462e35d35f9fbaf95c1e7da125d9` |
| `data/endpoint-graph/saved-cycle-audit.json` | `f8b7f079115d0f89f691130226f95897dfe70cb3d246b04473917efb9ba118f3` |

The result files and source are frozen. Existing milestone-121 evidence,
theorem sources, root documents and active proof jobs were left unchanged.
