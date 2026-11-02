# A new count restriction and its effect on the two bound calculations

Let a snake in the nine-dimensional cube have consecutive vertices
\(x_0,\ldots,x_m\). Keep the paper's existing notation \(\alpha_i\) for
the singleton-square count at an internal vertex. No new mathematical
definition is required in this round.

## Checked restriction

Suppose six consecutive transitions, after relabelling coordinates, have
directions \(0,1,2,3,4,0\). The five internal counts cannot be

\[
(5,5,2,4,5).
\]

Equivalently, when the transitions start at \(x_r\) and \(r+6\le m\),

\[
\alpha_{r+1}\ne5\quad\text{or}\quad
\alpha_{r+2}\ne5\quad\text{or}\quad
\alpha_{r+3}\ne2\quad\text{or}\quad
\alpha_{r+4}\ne4\quad\text{or}\quad
\alpha_{r+5}\ne5.
\]

The proof encodes necessary local conditions for an actual snake in a
radius-four neighbourhood. The encoding includes the selected path,
degree and endpoint conditions, and the specified count bounds. Every
clause used in the contradiction is checked against those conditions.
A finite contradiction then rules out the count pattern. The existing
coordinate-relabelling argument transfers the result to every actual
snake. Reversing the window reverses the order of its counts as well.

Lean checks the clause semantics, the contradiction, the statement about
actual snakes, and the forward and reverse applications to the graph
windows. The proof uses 1,664 clauses from a 59,251-clause formula; the
final contradiction has 2,007 deductions and 177,364 hints. An independent
replay also checks those deductions. This is a local restriction, with
no unproved catalogue assertion in its statement. The dependency objects
come from the previously audited environment; a clean rebuild of every
historical dependency is a separate outstanding task.

## Effect on the finite graph

The new restriction removes 865 additional accepted keys beyond the
2,092 exclusions from milestone 109. The separate restricted graph
therefore has 4,944,051 keys. One edge of the previously displayed
mean-483 cycle is removed. Other cycles attain the same mean.

Exact integer calculations give the following results. A potential is
checked against every remaining edge in each experiment; a matching
cycle attains each stated minimum mean.

| Experiment | Additional removed keys beyond milestone 109 | Completed-profile mean and range | Conditional-profile mean and range |
|---|---:|---:|---:|
| The one checked restriction | 865 | 483, 551 | 496, 602 |
| All seven proposed count restrictions | 4,773 | 483, 551 | 496, 602 |

The second row assumes six further exclusions which have not been
checked in Lean. All seven initial probes returned a native contradiction;
the probe for edge 2139224 used three additional cycle exclusions. The
other six used no additional cycle exclusions. None of these probes used
a cap on the empty-square contribution. The one checked restriction is
the case for edge 3534483.

The usual comparison remains

\[
(4200+P)m\le1098960+8P+R.
\]

For the two profiles it yields, respectively,

\[
m\le\frac{157625}{669}<236,
\qquad
m\le\frac{551765}{2348}<235.
\]

These are finite-graph comparison values. They give no new numerical
bound for snakes in this round: the original global prerequisites and
complete potential certificates remain separate. The maintained interval
is 191 through 235 edges, with the complete independent rebuild of the
contributor proof still pending. The conditional target remains 234.

## Consequence for further work

The broad scan of all 143 archived proof roots found no proposed relaxed
box that removes either original limiting cycle. Directly testing their
count patterns produced new local contradictions, but even assuming all
seven does not improve either numerical comparison. Adding hypothetical
empty-square contributions of at least 76 on those seven patterns also
leaves both comparisons unchanged.

The surviving completed-profile cycle has repeated count symbols
\((2,5,6,3)\), up to cyclic shift. Here symbol 6 still represents every
actual count from 6 through 21. The surviving conditional-profile cycle
has repeated count symbols \((4,3,5,4)\), up to cyclic shift. Their exact
directions, histories, and count encodings are saved with the results.
These are cycles of the finite model, without a claim that they are
realizable as snakes.

The next useful test is whether a single inequality or forbidden interval
of count values can exclude a family of these surviving configurations.
Test its effect on both full graphs before investing in a large proof.
Certifying the other six isolated cases is lower priority because their
combined numerical effect has already been tested. No claim of novelty
is made for the local restriction.
