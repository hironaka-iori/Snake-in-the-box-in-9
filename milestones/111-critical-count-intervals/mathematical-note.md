# Three-count restrictions and the remaining sum problem

Use the paper's existing singleton-square counts \(\alpha_i\). No new
mathematical definition is needed.

## A checked restriction

For any snake in the nine-dimensional cube, suppose six consecutive
transitions starting at \(x_r\) have canonical directions
\((0,1,2,3,4,0)\). Then

\[
\alpha_{r+2}\ge4
\quad\text{or}\quad
\alpha_{r+3}\ge3
\quad\text{or}\quad
\alpha_{r+4}\ge6.
\]

The first and fifth internal counts are unrestricted apart from their
usual range. The reversed window gives the corresponding reversed
restriction. This is a new family of exclusions on the same direction
shape as the previous exact-tuple theorem. Neither statement is presented
as a substitute for the other.

To prove the result, assume that the three middle counts are at most
\(3,2,5\), respectively. The selected path, degree conditions, endpoint
budget, count bounds and acyclicity then imply a finite system of Boolean
constraints. Thirteen additional cycle clauses arise from finite selected
vertex sets in which every vertex has at least two neighbours; acyclicity
justifies each such clause. The contradiction uses 2,040 clauses. Its
11,711 deductions and 611,907 hints pass an independent replay and Lean.
The geometric transfer to actual snakes and both graph orientations also
passes Lean. A clean rebuild of every historical dependency remains a
separate outstanding task.

The proof removes 1,462 additional accepted graph keys beyond milestone
110. The resulting separate graph has 4,942,589 keys. Both finite-graph
comparisons remain unchanged:

| Profile | Minimum cycle mean | Recorded potential range | Integer comparison |
|---|---:|---:|---:|
| Completed local inputs | 483 | 551 | 235 |
| Conditional local inputs | 496 | 602 | 234 |

Every remaining edge satisfies the saved potential inequality, and a
saved cycle attains each mean. These native graph calculations are
separate from a complete Lean certificate for the revised graph. They
give no improved numerical bound for snakes in this round.

## What the local witnesses rule out

The same local model admits the following exact count tuples:

\[
(11,4,2,4,9),\qquad
(11,3,2,6,12),\qquad
(12,4,2,5,9).
\]

Their selected sets have been independently checked for the local degree,
endpoint, acyclicity and count constraints. They prevent extending this
particular local proof to the middle bounds \((4,2,4)\), \((3,2,6)\) or
\((4,2,5)\). Boundary vertices retain the original local relaxation.
These sets are not constructions of complete long snakes, so they do
not disprove stronger statements that use additional global information.

## Candidate inequalities for sums

A more flexible hypothesis for the same direction shape is

\[
\alpha_{r+3}\le2
\quad\Longrightarrow\quad
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+4}+\alpha_{r+5}\ge22.
\]

The native solver reports a contradiction when the sum is at most 21.
Sorting repeated literals in an equivalent counter reduces the observed
probe time from about 13.5 seconds to about 2.0 seconds on this instance.
A complete native LRAT was obtained for that sorted encoding. An independent
replay checks its 71,388 deductions and 6,105,267 hints. Its
concrete count-sum semantics, Lean contradiction and transfer to actual
snakes remain pending. The generic counter-soundness argument needed for
that work has been checked, without adding mathematical definitions.

The repeated variables in the sum must retain their multiplicity: an
absent vertex can contribute to counts at several centres. Sorting those
occurrences preserves the constraint; removing duplicate occurrences
would change it.

The hypothesis was also tested in the finite graph. Counts represented
by symbols below 6 are exact. A symbol 6 can hide additional count above 6.
The proposed sum deficit can therefore justify either an exclusion or
an extra charge from those omitted counts. Charging only the suffix
window uses four fixed positions, so each position is counted at most
four times. At the current coefficient 120, this gives the candidate
coefficient 30 on the deficit. The existing share contribution must be
retained separately, and the boundary argument must be applied to the
counts clipped at 6.

Even assuming that inequality and its charge argument, the two graph
comparisons remain 483/551 and 496/602. The completed profile has another
limiting cycle with count period \((3,4,5,4)\), up to cyclic shift; the
relevant middle count is 3. The first probe with middle count at most 3
and outer sum at most 18 was unresolved after 20 seconds. Reordering the
repeated inputs subsequently produced a native contradiction in about
1.5 seconds, with no additional cycle cuts. That new result still needs
a checked certificate and semantic proof.

Combining this hypothetical sum restriction with the checked three-count
restriction still preserves both comparisons. Their additional deleted
sets are disjoint; the combined experiment removes 6,041 keys in total.
The displayed surviving cycles have every count symbol below 6, so a
bonus using only excess above 6 vanishes on them. Further progress needs
a condition that also addresses these unsaturated count patterns.

With the middle count unrestricted, the solver reports a contradiction
for outer sum at most 16. A separate checked local witness has counts
\((9,3,8,2,3)\), whose outer sum is 17. Thus 18 is already too strong for
an unconditional lower bound within this local model. The candidate
lower bound 17 still needs a checked contradiction. A continuous
relaxation for the middle-at-most-2 case has numerical optimum about 12.806;
that relaxation alone does not recover the conjectured integer bound 22.

The three proposed bounds were finally tested together: outer sum at
least 22 when the middle count is at most 2, at least 19 when it is at most 3,
and at least 17 without a restriction on the middle count. This experiment
also includes the checked three-count exclusion. It has 4,934,590 surviving
keys, after 7,999 further exclusions beyond the checked graph, and uses
the same coefficient 30 for excess.

For the completed profile, the minimum mean increases from 483 to
\(3384/7\), and the recorded potential range is \(3860/7\). The resulting
comparison is

\[
m\le\frac{1930913}{8196}<236.
\]

This is a small improvement in the conditional finite calculation; its
integer comparison remains 235. A saved fourteen-edge cycle attains the
new mean. The conditional profile still has mean 496, range 602 and integer
comparison 234. All-edge integer potential checks and matching cycles
support both calculations. None of the three sum hypotheses has yet
been proved for actual snakes in Lean, and their global excess-charge
integration remains pending.

## Remaining conclusions

The proved three-count restriction is usable now. The count-sum
inequalities remain hypotheses with separately saved computational
evidence. The original unsorted proof attempts and their timeouts are
preserved; they are not successful verifications.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit for 235 with its full independent
rebuild pending. Conditional 234, the exact optimum and the conjectured 196
remain unresolved. The reference union still has 1,366 unresolved entries.
The next useful work should examine the new fourteen-edge obstruction
and reduce the cost of certifying the three count-sum hypotheses. The
small fractional improvement supplies a reason to continue this family
of tests, while the unchanged integer comparisons limit what can be
claimed from the present evidence.
