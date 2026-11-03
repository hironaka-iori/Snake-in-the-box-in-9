# Milestone 140: a five-count exclusion

For every fitting canonical 012032 window in an actual snake in Q9,

\[
(\alpha_{r+1},\alpha_{r+3},\alpha_{r+5})=(3,4,3)
\quad\Longrightarrow\quad
\alpha_{r+2}\ge6\ \text{or}\ \alpha_{r+4}\ge6.
\]

This applies to either length parity and imposes no endpoint-location
condition. The counts are singleton-square counts at the five internal
vertices. No new mathematical definition is introduced.

## Evidence and proof

The bounded actual-path probe for exact counts (3,5,4,5,3) returned UNSAT
without extra cycle cuts. A separate fixed native proof run produced a
trimmed certificate with 18,606 deductions, 1,397,536 hints and 4,163 core
clauses. A complete independent Python RUP replay checked every deduction.
An independent reconstruction reproduced all 100,253 original clauses,
4,253 variable meanings and eleven count/endpoint tables.

The core never uses the lower bounds of five on the second and fourth
counts. Their 672 register variables occur in neither the core nor the
retained proof. Replacing those two unused counter entries by valid empty
endpoint counters makes the same clauses follow from the weaker intervals
[(3,3),(0,5),(4,4),(0,5),(3,3)]. The new semantic interpretation passed Lean.

The complete contradiction and actual-snake interpretation passed Lean.
The proof-completion record checks 120 CNF, semantic and contradiction
modules, the exact actual theorem, and the two weak-interpretation modules:
123 modules in this proof closure. The final semantic and actual sources
have eleven axiom reports using only propext, Classical.choice and Quot.sound.
The separate arithmetic module adds two such reports. No solver verdict
is used as an axiom. Exact sources, proof bytes, logs and hashes are retained.

Normalizing the window gives vertices 0,1,3,7,6,14,10. Each internal vertex
has twenty-one opposite corners in its seven unused directions. Its count
is the number of absent corners. The clauses express this count, the fixed
window, degree at most two, positive degree, at most two endpoints, and
ordinary square/six-cycle exclusions. These conditions are necessary for
an actual induced path. The checked contradiction excludes both intervening
counts being at most five; integer order then gives the stated disjunction.

## Consequence for the saved critical cycles

The exact count vector (3,5,4,5,3) occurs in two representations of the new
completed-profile five-cycle, edges 308566 and 3806548. The weaker theorem
also excludes (3,5,4,4,3), appearing on the earlier four-cycle at edges
2220858 and 146782. These are cycle deletions, not a new graph minimum.
The additional-share six-cycle contains no matching window and survives.
Its weight remains 496 per edge under the existing profile and credit.

The prepared evaluator reproduces the139 removal set and both weight
hashes, checks both six-direction placements and both orientations, and
requires every matching count symbol to be below six. Recognition overlap
causes one deletion and no added credit. Small preparation checks cover
7,776 count vectors and1,010 direction/placement combinations. The complete
graph evaluation has not been run in this milestone.

## Selected next optimisation

The earlier four-cycle forced a positive occurrence credit. Its removal
makes zero credit the next useful test. For mean496 and zero occurrence
credit, the comparison is below235 precisely when the potential range
R is below632:

\[
\frac{1098960+8\cdot496+R}{4200+496}<235
\quad\Longleftrightarrow\quad R<632.
\]

Lean checked the sufficient direction and the exact illustrative value
551765/2348<235 at R=602. The old range602 belongs to credit83/3; it is not
a zero-credit certificate. A new all-edge check is essential.

Next derive a fresh zero-credit evaluator from the saved140 preparation,
reproduce the139 inputs and apply only the checked weak deletion. Evaluate
both profiles. For the additional profile, the surviving six-cycle gives
mean at most496; seek a matching potential of range below632. The completed
profile's new minimum remains unknown. Keep the prepared credit83/3 version
as the pinned comparison; do not edit its audited bytes.

All inherited count-sum assumptions, the hypothetical0123104 six-count
floor25, the odd-length restriction behind pair floor9, and the additional
share assumptions remain. Complete graph-to-snake assembly and even-length
arguments are separate. No new conditional or unconditional actual-snake
upper bound is established here. The maintained interval is191–235, with
incomplete independent rebuilding of the contributor upper proof.
The optimum and196 remain unresolved. The research goal remains ACTIVE.

## Resume and document details

Read data/proof-completion.json, the independent semantic audit, and
scripts/complete_proof.py before using the new result. The original replay
driver has a known final-wrapper Mathlib path limitation; its completed
120 modules are retained, and the separate checker supplies the actual
library path for the final source. The unsuccessful directory-junction
attempt changed no proof or library bytes. Do not rerun the native solver
or completed replay merely to remove this recorded infrastructure failure.

Build objects are retained locally with audited hashes. The Git checkpoint
contains sources, proof inputs and certificates, receipts, exact compiler
snapshots and logs; regenerated build objects are excluded from publication.
The paper retains all three authors, its complete preamble and hyperlink
settings. Targeted revision140 adds no definitions. Last full revision136;
next full revision146. Compilation and PDF status are recorded separately.
The separate115 batch remains governed by its own live-process observation;
never start a duplicate driver.
