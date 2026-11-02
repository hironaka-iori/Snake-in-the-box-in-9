# A further restriction on four consecutive counts

Let five consecutive transitions of a snake in the nine-dimensional cube
use five distinct coordinate directions. For the four internal vertices,
the existing singleton-square counts satisfy

\[
\alpha_1\ge2\quad\text{or}\quad\alpha_2\ge6\quad\text{or}\quad\alpha_4\ge3.
\]

Thus the simultaneous conditions

\[
\alpha_1\le1,\qquad\alpha_2\le5,\qquad\alpha_4\le2
\]

are impossible. The third count is unrestricted within its natural range
from 0 to 21. The statement applies to an actual snake window, including
windows adjacent to an endpoint. The only length requirement is that all
five specified transitions exist. The reversed statement follows by reading
the window in the opposite direction.

The archived certificate concerned exact counts \((1,5,4,2)\). Its contradiction
uses 441 clauses. The count constraints retained in those clauses use only
the three upper bounds above, together with the existing endpoint constraint.
Five unused counter limits can be adjusted to the trivial bounds while all
clauses and variable interpretations remain fixed. The complete semantic
checker validates this adjustment. Combining it with the regenerated
contradiction proves the exclusion for the interval box

\[
[0,1]\times[0,5]\times[0,21]\times[0,2].
\]

The existing coordinate normalization and local-axiom transport then give the
stated theorem for every actual snake. Lean checks this composition and the
forward and reverse tests used by the six-count graph. This is a checked
strengthening of the archived restriction; no literature novelty is claimed.

The interval box contains four existing catalogue keys, with count symbols
\((1,5,4,2)\), \((1,5,5,1)\), \((1,5,5,2)\), and \((1,5,6,2)\).
Symbol 6 denotes every count from 6 to 21. Bounds containment supplies the
four exclusions. Together with the eight earlier entries, twelve entries
are checked. Lean proves that the original catalogue assertion is equivalent
to the assertion for the remaining 1,366 entries.

The earlier relaxed 012304 condition was tested first. Every one of the
4,947,008 accepted graph keys already avoids it, so that condition adds no
restriction to the present graph. Screening sixteen small archived cores
then identified the present 01234 condition as a stronger candidate.

In a separate calculation, the proved 01234 restriction removes 2,092 graph
keys, leaving 4,944,916. The full key includes direction, history and all six
count symbols; parallel graph edges are kept distinct. Every eligible
position and both orientations were tested. Both profiles use this same key
set, with their respective edge weights.

The restricted graph has the following exact finite-model results:

| Profile | Minimum cycle mean | Verified potential range | Integer comparison |
|---|---:|---:|---:|
| Completed local shares | 483 | 551 | 235 |
| Conditional local shares | 496 | 602 | 234 |

For each profile, a surviving cycle attains the stated mean, and exact integer
potentials verify the inequality on every remaining edge. These establish
the cycle means. The listed potential ranges are sufficient ranges; this
round does not prove that they are the smallest possible ranges.

The earlier paths obstructing a one-unit reduction of each pending share
floor also survive. With the other current floors fixed, the tested vectors
therefore retain their previous finite-model obstructions. This restriction
alone supplies no reason to reduce the pending floors
\((16,18,16,16,16)\).

The distinction between reducing the graph and improving its bound is
substantive here. Although 2,092 accepted configurations are impossible for
actual snakes, the sharp cycles remain. All sixteen screened relaxed boxes
miss both sharp cycles. Moreover, Lean checks

\[
(4200+P)235\le1098960+8P+R\qquad(P\le483,\ R\ge0),
\]
\[
(4200+P)234\le1098960+8P+R\qquad(P\le496,\ R\ge0).
\]

Thus reducing the potential range alone, even to zero, cannot improve either
integer comparison while the corresponding cycle mean remains. The next
source screen should therefore test those
cycles first and replay a candidate with a verified effect on them. A
certificate covering many catalogue entries can still shorten the proof,
but its numerical benefit must be assessed separately.

The maintained interval remains \(191\le a(9)\le235\) edges. The upper endpoint
retains its inspected contributor proof and archived audit, with a complete
independent rebuild pending. The restricted graph calculation is separate
from the running proof of the original graph. It does not supply a complete
new graph certificate or a new global upper bound. The exact optimum and
the conjectured value 196 remain unresolved.
