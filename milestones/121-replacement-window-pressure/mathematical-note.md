# A sharp two-count bound and a possible endpoint restriction

Let $p_0,\ldots,p_m$ be a snake in $Q_9$. Retain $\alpha_i$ for the number of
coordinate squares containing $p_i$ and no other selected vertex. If the six
directions beginning at $p_r$ are $(a,b,c,a,d,c)$, where $a,b,c,d$ are distinct,
then

$$
\alpha_{r+2}\ge2,\qquad \alpha_{r+4}\ge2,\qquad
\alpha_{r+2}+\alpha_{r+4}\ge8.
$$

There are no further count hypotheses. The sum bound and the two separate
lower bounds are Lean checked. The sum bound is sharp for complete snakes.
These are local restrictions; they do not determine the longest snake.

## Proof

Translation and coordinate relabelling give the window
$(0,1,3,7,6,14,10)$. Three finite contradictions exclude the following upper
caps on the second and fourth internal counts:

| Second count | Fourth count | Deductions | Hints |
| ---: | ---: | ---: | ---: |
| $1$ | $21$ | 144 | 2,081 |
| $2$ | $5$ | 1,328 | 71,339 |
| $3$ | $4$ | 4,683 | 289,344 |

The other three counts are unrestricted within their general interval $[0,21]$.
Each contradiction uses the radius-three geometric encoding with no added
cycle cuts. A separate plain encoder gives identical clauses, and independent
native replay checks all deductions. Lean checks the concrete clause
interpretations and refutations.

Reversing this direction word and relabelling gives the same word. Thus each
excluded pair also excludes its reversal. The first row gives both counts at
least two. If their sum were at most seven, ordering the two counts would put
them under either $(2,5)$ or $(3,4)$. The remaining rows exclude these cases.
The checked actual-snake argument includes this reversal and finite case split.
A short direct geometric proof of the three rows has not been obtained.

## Attainment by actual snakes

The three full-cube searches returned complete induced paths with the following
designated windows. An independent reconstruction checks all 30,184 unordered
vertex pairs and recomputes all five singleton-square counts.

| Path length in edges | Window start | Five counts | Second–fourth pair |
| ---: | ---: | --- | --- |
| 142 | 120 | $(10,2,8,6,12)$ | $(2,6)$ |
| 138 | 114 | $(13,3,12,5,12)$ | $(3,5)$ |
| 144 | 136 | $(12,4,12,4,13)$ | $(4,4)$ |

All three witness modules pass Lean, including actual inducedness, the canonical
window, exact pair counts and attainment. The $(2,6)$ witness proves that the
sum eight and the individual minimum two cannot be increased for all snakes
of this shape.
These paths do not improve the longest known construction.

The older bank of 131 paths contains 53 matching windows, whose smallest pair
sum is 16. The new witnesses show why that finite bank cannot justify replacing
eight by sixteen in a universal statement.

## Effect on the finite graph

The pair restrictions remove 14,646 additional transitions beyond milestone120.
They exclude two edges of the previous conditional five-cycle. A replacement
four-cycle has the same mean 496 and potential range 602. The other profile's
eighteen-cycle survives with mean $2915/6$ and range $1730/3$. The corresponding
integer comparisons remain 234 and 235. Both experiments retain their existing
unproved sum hypotheses and global proof obligations.

The new conditional cycle contains $012032$ windows with pairs $(3,5)$ and
$(5,3)$. These attain the sharp bound. Increasing the universal pair constant
would contradict the complete witnesses above. Further progress must use
additional conditions or control how often equality can occur.

Five direct reference-catalogue entries are now Lean checked as consequences
of the pair exclusions. Twenty entries in total are discharged; exactly 1358
remain. The complete reference premise is still unresolved.

## Endpoint hypothesis and conditional consequences

In all three new witnesses, both endpoints are at Hamming distance two from
both counted vertices. This suggests the following hypothesis:

> If a $012032$ window has $\alpha_{r+2}+\alpha_{r+4}=8$, both endpoints of the
> snake have distance two from each of $p_{r+2}$ and $p_{r+4}$.

For each boundary pair $(2,6)$, $(3,5)$ and $(4,4)$, a full-cube search requiring
at least one endpoint outside the intersection of these two distance-two spheres
returned UNSAT, without cycle cuts. The base encodings and added endpoint
clauses have been audited. No refutation replay or Lean proof of this endpoint
hypothesis is yet available. Reversal would cover the other two ordered boundary
pairs once the necessary semantic argument is checked.

Two consequences would follow if the hypothesis is proved:

1. Equality can occur only in a snake of even edge length. Vertices at even
   Hamming distance have the same bipartite colour, so the endpoints would have
   the same colour. Every snake of odd edge length would satisfy the stronger
   pair sum lower bound nine.
2. There can be at most fourteen equality windows in any snake. Each first
   counted vertex would lie at distance two from both endpoints, and different
   starts give different first counted vertices. For distinct endpoints at
   distance two, their distance-two spheres intersect in fourteen vertices;
   at distance four the intersection has six vertices; at other distances it
   is empty. After translating one endpoint to zero, the intersection count is
   $\binom{d}{d/2}\binom{9-d}{2-d/2}$ for $d=2,4$. A separate enumeration checks
   all 511 nonzero endpoint differences. The general count and frequency
   arguments remain to be integrated in Lean.

The second consequence would permit adding a nonnegative credit $C$ to each
matching graph occurrence, with total correction at most $14C$. In the existing
potential notation, the resulting conditional comparison is

$$
(4200d+p)m\le1098960d+14Cd+8p+R.
$$

Its conditional arithmetic passes Lean in `EndpointArithmetic121.lean`.
The endpoint hypothesis, occurrence bound and modified graph potential remain
separate obligations. For an initial graph test, count only the exact pairs
$(3,5),(4,4),(5,3)$. A clipped pair $(2,6)$ may represent an actual pair sum
larger than eight and cannot receive this endpoint credit without another argument.

The next selected task is to certify the three endpoint contradictions, prove
their actual-snake interpretation and the occurrence bound, then evaluate this
credit on both graph profiles. The maintained interval remains
$191\le a(9)\le235$; neither a new global bound nor the exact optimum is claimed.
