# The next shared count restriction: a local obstruction and a limit

Consider six consecutive directions $012301$, with the existing singleton-square
counts $\alpha_{r+1},\ldots,\alpha_{r+5}$ at the five internal vertices. The
normalized window is $(0,1,3,7,15,14,12)$.

The proposed inequality

$$\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge13$$

fails for the radius-four local model, even if $\alpha_{r+3}\ge6$. Two
independently checked forests have counts $(4,2,10,2,3)$ and $(4,2,10,4,2)$,
whose outer sums are 11 and 12. Their clipped counts exactly reproduce both
critical $012301$ tuples of milestone 117. The middle symbol 6 must retain
its full interval $[6,21]$.

The first forest has 117 vertices in seven path components; the second has 113
vertices in four components. Each has two interior endpoints. Their remaining
component ends lie on the boundary of the local ball. These facts exclude
using the proposed inequality as a consequence of the current local constraints.
They leave the corresponding actual-snake question unresolved. Separate local
witnesses do not establish simultaneous realization of a full critical cycle.

The total-count witnesses $(3,2,5,4,4)$ and $(4,3,6,2,4)$ have totals 18 and 19.
The first disproves a local total lower bound 19; the second disproves a local
total lower bound 20 even with middle count at least 6. Bounded searches leave
both the following hypotheses unresolved:

$$\sum_{j=1}^{5}\alpha_{r+j}\ge18,$$

$$\alpha_{r+3}\ge6\quad\Longrightarrow\quad
\sum_{j=1}^{5}\alpha_{r+j}\ge19.$$

A timeout or a remaining cyclic assignment proves neither hypothesis.
The resumed searches retain every previously validated cycle exclusion.

Suppose both hypotheses were available. With existing coefficients $a,c\ge0$
and $4a+c\le120$, the coefficient of a five-count deficit is $\min(a,c)\le24$.
The applicable credits use their maximum; adding them would count the same
excess twice. Each old cycle has one affected suffix window. The completed
cycle has clipped total 17 and hence deficit 2; the conditional cycle has
clipped total 18 and deficit 1. Their middle symbol 6 prevents deletion by a
sum restriction, since the actual middle count can exceed its clipped value.
Every older applicable deficit is zero on these cycles.

Consequently these retained cycles give the ceilings

$$\frac{8745+2\min(a,c)}{18}\le\frac{977}{2},\qquad
\frac{1488+\min(a,c)}{3}\le504.$$

These are upper limits on the best attainable minimum means in this fixed
hypothetical family. No new all-edge potential or matching minimum is asserted.
At zero potential range, excluding length 235 requires $227p>111960d$;
excluding 234 requires $226p>116160d$. At the two ceilings,

$$111960\cdot2-227\cdot977=2141>0,$$
$$116160-226\cdot504=2256>0.$$

A nonnegative potential range only makes those exclusions harder. Thus these
two sum hypotheses alone cannot improve the integer comparisons, even if they
are eventually proved. This conclusion concerns the stated shared-budget
family and leaves stronger local restrictions or other global arguments open.

Lean checks the concrete count tuples, the disjoint induced path components,
and the five coefficient/comparison deductions. The radius-four and interior
endpoint checks remain independently verified computations. Four private Lean
constants hold the repeated concrete path data; they introduce no mathematical
concept. The first attempted larger combined check timed out and is preserved.

The next test should concern the shared shape $012304$. Its two large count
symbols must remain intervals, and any proposed new credit should first be
compared against both saved cycles before exporting a large certificate.
