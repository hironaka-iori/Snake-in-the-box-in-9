# Milestone 149: uniform credit cannot replace the share-16 target

For the original graph with 4,947,008 transitions, lowering the 012032 share
floor to 15 prevents the existing comparison from reaching below 235 for
every uniform occurrence credit. The other eight floors and the occurrence
allowance 24 are fixed. This is a limitation of one graph argument.

The new 28-edge walk, an eleven-cycle and an unchanged three-cycle imply

\[
\mu\le496,\qquad11\mu\le5452+4C,\qquad28\mu\le13280+R.
\]

Lean checked that these inequalities force the comparison to be at least
235, together with four supporting arithmetic statements. The saved graph
identities are checked separately; the Lean file assumes the displayed
inequalities and imports no graph certificate.

Read [the mathematical note](MATHEMATICAL_NOTE.md),
[the graph review](audit/graph-review.md), and
[the Lean receipt](data/CreditTradeoff149-audit.json).
The two bounded numerical experiments and their exact inputs are retained.
No half-credit experiment was run: the combined obstruction made it unnecessary.

The original full 147 contradiction replay continues in session 67526,
coordinator PID 15228 at this checkpoint. The conditional actual-snake
share-16 transfer completed in 148 remains available. Its complete core
contradiction and final composition remain pending. No new global bound
is claimed; the goal remains active.
