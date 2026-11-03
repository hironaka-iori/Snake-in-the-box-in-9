# What the full comparison changes

The experiment uses the proved pair bound nine for odd-length snakes and a
proposed six-count lower bound twenty-five for direction shape 0123104.
The previous removal list and both complete weight vectors were reproduced
before applying the new constraints. The resulting graph has 1,601,856 states
and 4,661,773 retained edges. The pair condition removes 14,771 edges, and the
six-count condition removes another 6,570.

## Exact finite-model results

| Profile | Previous minimum | New minimum | Previous comparison | New comparison |
|---|---:|---:|---:|---:|
| Completed share catalogue | \(2915/6\) | \(488\) | \(1324108/5623\) | \(1103449/4688\) |
| Additional share assumptions | \(496\) | \(496\) | \(551765/2348\) | \(551765/2348\) |

The first comparison is approximately 235.37735; the second is approximately
234.99361. Their integer parts remain 235 and 234. The first profile's name
refers to its share catalogue. Its inherited count-sum hypotheses remain
unproved, and the proposed six-count inequality is also unproved.

The evaluator verifies integer-potential inequalities on every retained edge
and a closed cycle attaining each minimum. The independent review reconstructs
both cycles from the original graph rows, checks their weights and adjacency,
and checks the full saved potential hashes and ranges. It does not repeat the
full all-edge calculation. These are exact native finite-model results; the
complete Lean graph verification and transfer to arbitrary snakes remain open.

## Why the selected pattern cannot give further progress alone

The cycles attaining 488 and 496 avoid 0123104. Increasing its proposed bound
from twenty-five upward can only increase some weights and delete some edges.
Thus the existing potential inequalities remain valid. The two displayed
cycles remain present with unchanged weights, so they still attain the same
minima. This conclusion concerns this fixed finite model and this single
change to its assumptions.

Even an ideal potential range of zero would give

$$
\frac{68929}{293}=235+\frac{74}{293}>235,
\qquad
\frac{137866}{587}=234+\frac{508}{587}>234.
$$

Consequently, strengthening only this pattern cannot produce the next integer
comparisons 234 and 233 through the existing formula. The elementary
monotonicity deduction is written and independently reviewed; it is not a
new Lean-certified assertion about arbitrary snakes.

## The remaining four-edge cycle

All four seven-direction windows have canonical shape 0120324 after allowing
reversal. Counts below are put in that canonical orientation; all are exact.

| Edge | Six counts | Total | Second plus fourth |
|---|---|---:|---:|
| 2222328 | \((4,5,3,4,4,5)\) | 25 | 9 |
| 147674 | \((4,4,3,5,4,4)\) | 24 | 9 |
| 2220858 | \((3,4,4,5,3,4)\) | 23 | 9 |
| 146782 | \((3,5,4,4,3,5)\) | 24 | 9 |

The fourth count is four or five, so the completed fourth-count-three theorem
does not apply to these windows. Each relevant pair attains the new lower
bound nine. A restriction on how often this equality occurs could therefore
address this cycle. No actual snake realizing the cycle has been constructed.

The other profile's seven-edge cycle has no matching 012032 pair window. Its
seven-direction shapes are 0123045, 0123014 and 0123042. The proposed endpoint
test therefore addresses the first obstruction only.

## Next hypothesis and its first test

For odd \(m\), consider the following implication in a fitting 012032 window:

$$
\alpha_{r+2}+\alpha_{r+4}=9
\quad\Longrightarrow\quad
\exists e\in\{0,m\},\quad
d_H(p_{r+2},p_e)=d_H(p_{r+4},p_e)=2.
$$

This remains a hypothesis. The two centres have the same parity, while an
odd-length snake has endpoints of opposite parity. Hence at most one endpoint
can satisfy the displayed conclusion. If the implication holds, repeated
equality windows could be counted through the vertices at distance two from
the two endpoints. No occurrence bound from this hypothesis is yet claimed.

A cheap screen independently validated 133 distinct saved vertex sequences,
including the explicit 191-edge construction, a bank of 131 snakes, and a
120-edge endpoint witness. All 54 matching windows had pair sums different
from nine. The test is therefore vacuous for the implication; absence of a
counterexample here supplies no supporting evidence.

The selected next test normalizes the window to
\((0,1,3,7,6,14,10)\), retains the multiplicity of the 42 opposite-corner
occurrences, imposes pair sum at most nine, and requires an endpoint of each
vertex parity. It forbids endpoint flags at the fourteen vertices that are
at distance two from both 3 and 6. A genuine path satisfying this input would
refute the hypothesis. A negative native search would still require a complete
certificate and an actual-snake interpretation. Disconnected cycle components
must be excluded by valid cycle cuts before a selected set is called a path.

No new definition is introduced. The global interval and its independent-proof
limitation are unchanged. The paper is at revision 126; its next full revision
is due at 136.
