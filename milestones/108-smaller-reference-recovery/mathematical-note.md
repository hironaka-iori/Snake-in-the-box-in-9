# A restriction using three of five counts

Consider seven consecutive vertices with transition directions 012304, where
the symbols designate five distinct coordinate directions. Write the existing
singleton-square counts at the five internal vertices as
\(\alpha_1,\ldots,\alpha_5\). Each count lies between 0 and 21.

Under the existing local necessary conditions for a normalized snake window,
the following simultaneous inequalities are impossible:

\[
\alpha_1\le2,\qquad \alpha_4\le2,\qquad \alpha_5\le3.
\]

Equivalently, at least one of

\[
\alpha_1\ge3,\qquad \alpha_4\ge3,\qquad \alpha_5\ge4
\]

must hold. The second and third counts are unrestricted within their natural
range. This is a checked relaxation of an archived exclusion, with no claim
that the combinatorial observation is new in the literature.

The archived entry specified the more restrictive intervals

\[
(\alpha_1,\ldots,\alpha_5)
\in\{2\}\times\{2\}\times[6,21]\times\{2\}\times\{3\}.
\]

Its contradiction uses 120 clauses selected from a 29,055-clause formula.
Inspection shows that its count clauses use only the three upper bounds
displayed above. Merely dropping the other assumptions from the theorem
would be insufficient: the semantic checker also validates the metadata
of unused counters. Six such counter limits were therefore adjusted to the
trivial bounds, preserving all clauses, variable meanings and counter positions.
Lean checked the entire semantic interpretation with the relaxed intervals

\[
[0,2]\times[0,21]\times[0,21]\times[0,2]\times[0,3].
\]

The regenerated contradiction remains unchanged. Combining the two checked
arguments proves the relaxed exclusion. The proof consists of 75 retained
unit-propagation deductions using 426 antecedent references; a separate
plain-clause checker also validates them.

The seven exact catalogue entries covered by this exclusion have count
symbols

\[
\begin{gathered}
(2,2,6,2,3),\ (2,3,6,2,3),\ (2,4,6,2,3),\ (2,5,6,2,3),\\
(2,6,4,2,3),\ (2,6,6,2,2),\ (2,6,6,2,3).
\end{gathered}
\]

As throughout the catalogue, symbol 6 denotes the interval from 6 to 21.
Each listed set of intervals is contained in the relaxed set. A checked
general argument transfers a refutation to tighter bounds at the same
vertices and directions. It supplies all seven exclusions without seven
separate contradiction replays.

The earlier exclusion for direction word 012 with counts (1,1) supplies an
eighth reference entry. Lean checks both the equivalence between the full
catalogue assertion and the assertion after removing these eight entries,
and the remaining length 1,370. This establishes the exact scope of the
recovery. The full catalogue remains an outstanding proof obligation.

The local statement retains the established degree, endpoint, acyclicity and
window assumptions. The general actual-snake transport remains in the existing
bridge. This round checks the local restriction and its use in the exact
reference catalogue; it does not install a new graph filter or prove a
stronger global upper bound.

The next useful test is whether this relaxed exclusion removes any currently
accepted full graph keys, in either orientation and at every eligible window
position. If it does, quantify its effect on both potential profiles in a new
experiment. If it does not, inspect other small archived cores for unused
count assumptions and rank them by the number of remaining keys they cover.
These are untested continuation steps.

The maintained interval remains \(191\le a(9)\le235\) edges. The upper endpoint
uses the inspected contributor proof and archived audit, with a complete
independent rebuild pending. The conditional target 234 additionally needs
the complete graph certificates and five local share bounds with floors
\((16,18,16,16,16)\), as well as the remaining reference exclusions.
