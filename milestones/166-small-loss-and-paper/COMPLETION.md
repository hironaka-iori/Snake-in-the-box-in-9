# Round 166: exact small-loss restrictions and zero-loss countermodels

Six finite arithmetic statements passed Lean with no axioms. They cover
all possible Q9 degrees and incident-square counts, conditional on the
geometric bound e(q) <= choose(9-d(q),2). The geometric bound is proved
in the paper by assigning each empty square its two absent-neighbour
directions; that geometric interpretation is not newly checked in Lean.

Loss at most three excludes positive empty-square counts at degrees zero
and seven, excludes count two at degree five, and permits at most three
positive degree-five residues. Count five at degree five has zero residue.

The independent exact audit checks the explicit 191-edge snake (loss 163)
and all 131 bank snakes (loss 152 through 913). It also gives zero-loss
countermodels: a disconnected degree-two set; a disconnected set with
exactly two endpoints and cycles; an acyclic set with 64 endpoints; and a
union of sixteen six-cycles. None is a snake or a counterexample at 235 edges.
Thus no universal positive-loss bound has been established.

The existing paper and its repository mirror were updated in place,
reviewed against all 6,605 prior lines, and compiled by the editor. The
preamble, local hyperlink settings, and three authors were preserved.
The update integrates the exact loss budget, degree decomposition,
conditional 234 comparison, finite tests, and current replay status.
The first compilation returned stale-project; the retry succeeded.
The six Lean checks used the core library with a separate small-memory
profile. The initial core startup gate stopped before compilation; the
later run passed. The large replay's original resource limits remain
unchanged. Its accepted prefix is still 33,111 deductions.

Read experiment/FINDINGS.md for constructions, data/completion.json for
scope and hashes, and review/full-paper-review.md for the source review.
Last full paper revision: 166. Next scheduled full revision: 176.
