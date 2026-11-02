# Geometric credit integration and least pending share requirements

The global interval remains
\[
191\le a(9)\le235.
\]
The upper bound retains the inspected contributor theorem and archived audit;
a complete independent rebuild is pending. The improvement to 234 remains
conditional. This note records a reduction in its local proof requirements
and the separate integration of already checked geometric bounds.

## Least requirements within the current finite graph

The fixed graph has 4,947,008 edges. Its existing credits, state transitions,
history rules and four completed target floors remain unchanged. Consider
lowering only the five unfinished count-independent floors, each to a
nonnegative integer no larger than its original target. Credits are in the
existing scale-12 units and concern the five internal centres of the canonical
six-direction window, with reversal treated as the same shape.

The least sufficient values for the current 234 comparison are:

| Shape | Original target | Least required value in this graph argument |
| --- | ---: | ---: |
| 012032 | 16 | 16 |
| 012034 | 20 | 18 |
| 012301 | 16 | 16 |
| 012340 | 16 | 16 |
| 012345 | 16 | 16 |

More precisely, in this order the feasible vectors within the original target
box are exactly
\[
(16,h,16,16,16),\qquad h\in\{18,19,20\}.
\]
Here feasibility means that a constant slope and a potential with a global
range satisfy the graph-edge inequalities and the existing arithmetic
criterion for an upper comparison strictly below 235. This statement concerns
the saved finite graph and its fixed boundary accounting.

### Sufficiency

For the vector with $h=18$, the saved potential satisfies
\[
496+\pi(v)\le w(u,v)+\pi(u),\qquad 0\le\pi\le602
\]
on every edge. Independent integer verification checks all 4,947,008
inequalities. A three-edge cycle of weight 1488 attains mean 496.

If the local credit interpretation, graph coverage and global charge premises
are supplied, write $W$ for the total weight of the $m-8$ graph edges traced
by an $m$-edge snake. For $m\ge9$, it satisfies
\[
496(m-8)\le W+602,\qquad W+4200m\le1098960.
\]
Adding gives
\[
4696m\le1103530,\qquad
m\le\frac{551765}{2348}=235-\frac{15}{2348}<235.
\]
The strict margin at $m=235$ is 30. Increasing a floor can only increase edge
weights, so this potential also suffices for $h=19,20$. Range 602 is a verified
sufficient range; its optimality is not asserted.

### Necessity

Each test below keeps all other original target floors fixed. It preserves
the three-edge cycle of mean 496 and supplies an open walk with the listed
length and weight.

| Shape weakened | Tested floor | Walk length $k$ | Weight $C$ | $496k-C$ |
| --- | ---: | ---: | ---: | ---: |
| 012032 | 15 | 69 | 33592 | 632 |
| 012034 | 17 | 51 | 24663 | 633 |
| 012301 | 15 | 94 | 45992 | 632 |
| 012340 | 15 | 77 | 37560 | 632 |
| 012345 | 15 | 36 | 17224 | 632 |

For any admissible slope $p$ and global potential range $R$, the cycle gives
$p\le496$ and the open walk gives $kp-C\le R$. Since $k\le227$,
\[
227p-R\le(227-k)p+C
\le(227-k)496+C\le111960.
\]
The current 234 criterion requires $227p-R>111960$, so none of these five
test profiles can work with any constant slope or global potential range.

Every vector in the original target box that violates one of the proposed
lower limits has weights no larger than the corresponding failed test.
A potential valid for those smaller weights would remain valid for the test
weights, contradicting the obstruction. This proves necessity for simultaneous
reductions, without enumerating every vector. Increasing a floor acts through
$\max(\text{previous weight},120b+\text{floor})$, with every edge key unchanged.

### Proof boundary and practical consequence

The finite witnesses and potential are independently verified integer data.
The general charge arithmetic, path obstruction and monotonicity arguments
have passed Lean, with successful compiler and axiom-audit receipts. The full finite potential and witness tables have not
been replayed in Lean. A graph walk is not asserted to occur inside a complete
snake. Changed graph restrictions, stronger credits outside the target box,
or better boundary estimates can change this conclusion.

The most economical 012034 target for this argument is therefore share at
least 18, which requires excluding share at most 17. That local theorem is
still unproved here. The old case7302 source and stopped replay for the
stronger target 20 are preserved. A fresh weaker local problem must be kept
separate from that evidence. No proof-time improvement has been measured.

## Actual geometric and history credits

The geometric table has 505 canonical nine-direction shapes: 357 positive
credits and 148 zero credits. Its direction order agrees exactly with the
current graph dictionary. The existing positive proofs charge centres
$r+4,\ldots,r+8$ of a window satisfying $r+9\le m$.

The integration decodes the actual direction index, uses the existing
coordinate-permutation argument, and applies the corresponding local
inequality. Zero entries follow from nonnegativity. No stronger local
geometric assertion is substituted for an existing proof. The source ports
change only import lines so that they use the current share declarations.

The same five-centre sum bounds the completed 55-rule history credit. Their
maximum is therefore bounded by that sum. The entering truncated count
satisfies $b_{r+8}\le\alpha_{r+8}$, including when its symbol is six. Hence
the geometric/history part of an actual edge weight is at most
\[
120\alpha_{r+8}+\sum_{j=4}^{8}\sigma_{12}(x_{r+j}).
\]
The complete catalogue and its actual-window assembly have passed Lean.
This result does not by itself include the four count-conditioned credit
rules, share 120, the selected count-free profile, or the global potential.

The checked generic count-conditioned theorem separately transfers a canonical
direction match and its exact count symbols to the same five centres. Its
reverse transfers both lists. Symbol six retains the interval $[6,21]$;
it is never replaced by the equation $\alpha=6$. The concrete closed local
refutations still need to instantiate these interfaces in the common
environment.

## Completed graph coverage

All 127 geometric coverage classes and all 127 witness classes passed their
checks. The final assembly proves that an actual snake traces a walk in the
defined graph, assuming the two stated reference-catalogue refutations. These
assumptions remain explicit. The remaining weight components, local share
requirements and complete potential on this graph are separate obligations.

## Evidence

The checking status and exact sources are recorded in `data/proof-summary.json`
and the individual Lean receipts. `floor-sensitivity/verification.json`
checks all five one-unit tests. `floor-sensitivity/012034-minimum/verification.json`
checks the sharp 18/17 threshold and its full-edge potential. Original proof
sources, generated adapters, successful logs and unresolved dependencies are
preserved in this milestone.
