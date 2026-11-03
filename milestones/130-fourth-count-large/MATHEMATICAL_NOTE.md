# A stronger pair inequality from parity

For a snake with \(m\) edges and a fitting canonical direction window
\(012032\) beginning at \(r\), the following implication is now checked
in Lean:

$$
\alpha_{r+2}+\alpha_{r+4}=8
\quad\Longrightarrow\quad
m\equiv0\pmod2\quad\text{and}\quad r\equiv0\pmod2.
$$

Together with the previously proved pair lower bound eight, this gives

$$
\alpha_{r+2}+\alpha_{r+4}\ge9
\qquad\text{if }m\text{ or }r\text{ is odd}.
$$

In particular, every fitting \(012032\) window of a snake with 235 edges
satisfies the stronger lower bound nine. These statements concern actual
snakes and have no unproved local-certificate premise.

## Proof

The completed endpoint theorem states that equality of the pair sum to eight
places both endpoints at Hamming distance two from each of the two specified
centres. A change in two cube coordinates preserves binary-weight parity.
Thus the two endpoints and the centre at position \(r+2\) have the same
parity. Each edge of a snake reverses parity. It follows that both \(m\)
and \(r+2\) are even, and hence that \(r\) is even.

If \(m\) or \(r\) is odd, equality to eight is impossible. The pair sum
is an integer already known to be at least eight, so it is at least nine.

The Lean proof uses induction on Boolean lists to establish the parity rule
for coordinatewise addition. The existing path-parity argument was rebuilt
from its exact source. The new module has eight successful axiom reports;
the rebuilt dependency has four. No new mathematical definition is needed.

## Consequences for the saved cycles

The comparison uses the original saved eighteen-edge and four-edge witnesses.
It does not assert that either witness is realizable by an actual snake.

For odd-length snakes, the pair bound nine removes all four edges of the
four-edge witness. For even-length snakes, the odd-start restriction removes
one of its two initial parity choices; the other survives this test.

The surviving choice contributes two distinct equality windows per complete
four-edge period. The completed endpoint theorem allows at most thirteen
such starts in an actual snake. Seven complete fitting periods would therefore
give fourteen starts and are excluded, provided the graph occurrences are
transferred to those actual windows. Counting suffix placements only avoids
counting the same window again in a neighbouring edge.

The eighteen-edge witness contains no matching \(012032\) window. Its
mean \(2915/6\) is unchanged by both parity restrictions and the occurrence
budget. Consequently these restrictions alone do not remove that obstruction
to the existing comparison. No full graph recomputation or new global upper
bound is asserted by the saved-cycle check.

## Complementary six-count case

The ongoing six-count target on canonical shape \(0120324\) is

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge23.
$$

This round tested the case \(\alpha_{r+4}\ge4\) under the contrary total
bound 22. It retains the valid pair bound eight and the necessary intervals

$$
([1,21],[2,21],[1,21],[4,21],[1,21],[1,21]).
$$

The stronger first and second count bounds from the fourth-count-equals-three
case are not premises here. Nor is the three-count upper bound eleven.

At the fourth centre, at most seventeen of the twenty-one opposite corners
are selected. Lean checks this conversion and satisfaction of all 717 added
counter clauses for actual snakes. This establishes the added constraint's
meaning. It does not establish a contradiction of the full input.

The resumed search reached its 300-second limit without a model or a
contradiction. Its measured process CPU time was 29.546875 seconds. Independent
replay checked the first 5000 deductions of each saved incomplete trace.
The initial attempt was interrupted with no recorded terminal status; it
must not be described as a solver timeout. All original bytes are retained
and also preserved in verified lossless archives.

<!-- BEGIN EQUALITY STATUS -->
The full 221-module contradiction replay and the final application to actual
snakes have now passed Lean. For every fitting canonical 0120324 window,

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

The existing first-count lower bound three and second-count lower bound five
then give

$$
\sum_{j=1}^{6}\alpha_{r+j}\ge 3+5+3+12=23.
$$

Thus any such window with six-count total at most 22 must have fourth count
at least four. The final three checked statements have no remaining
local-certificate premise. This closes the equality case only.
<!-- END EQUALITY STATUS -->

## Next selected experiment

The surviving eighteen-edge witness uses four seven-direction shapes. The
shape \(0123104\) occurs ten times. Among the four single-shape tests, granting
a six-count floor 25 for this shape gives the largest increase in that saved
witness's weight. Using the established exact-first-count guard and taking
the maximum of overlapping credits increases its total weight by 288,
changing this particular cycle's mean from \(2915/6\) to \(3011/6\).

This is a hypothetical recalculation of one witness. It is not a new minimum
mean for the graph. A previous native search for a six-count total at most
24 on \(0123104\) was negative, but its certificate and actual-snake transfer
have not been completed.

The next selected experiment is to recompute both graph profiles with the
proved odd-length pair bound nine and the proposed \(0123104\) six-count
floor 25. The recomputation must preserve the full meaning of clipped count
six, the common coefficient budget, and every inherited unproved hypothesis.
Only an actual improvement in the full graph would justify selecting that
local certificate for further verification.

The maintained range remains \(191\le a(9)\le235\), with the documented
independent-rebuild limitation on the contributor upper-bound proof. The
optimum and the proposed value 196 remain unresolved. The paper remains at
revision 126; the next scheduled full revision is 136.
