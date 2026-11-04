# Two-round stopping point: small loss and undominated corners

Rounds 166 and 167 are complete. Research stops here for the requested
bounded continuation. No research worker remains running.

Round 166 checked six finite degree/remainder statements in Lean, audited
all 131 saved 191-edge snakes, and produced explicit zero-loss disconnected
countermodels. The complete paper received its scheduled revision and
compiled successfully with its original preamble, hyperlink settings,
and authors preserved.

Round 167 gives a written geometric proof: if every selected vertex has
degree one or two, an undominated cube vertex lies on at least four empty
squares. Equality forces eight selected degree-one vertices. Hence for a
nontrivial snake, an undominated vertex lies on at least five empty squares
and contributes at least 60 to total rounding loss. Therefore total loss
at most 59 forces every cube vertex to have a selected neighbour.

Six supporting logical and arithmetic statements passed Lean. The full
Q9 interpretation, coverage/matching counting, distinct endpoint count,
and global-sum assembly remain pending. The written theorem must not be
labelled a complete Lean-checked arbitrary-snake theorem. The degree-only
bound four has an exactly checked 60-vertex equality example with eight
endpoints; it is disconnected and is not a snake.

The target loss-at-most-three case is thus restricted to dominating
snakes. This does not exclude it. The printed 191-edge witness already
has this domination property. There is no new numerical upper bound.
The earlier conditional 234 comparison still needs its loss and inherited
geometric/certificate premises. The large replay remains at 33,111 checked
deductions; no new replay deductions were attempted in these two rounds.

Read milestones/167-undominated-corners/COMPLETION.md and its adjacent
data/completion.json for the exact scope. The full proof appears in
review/PROOF_REVIEW.md and in the updated paper. Last full paper revision:
166; latest mathematical addition: 167; next scheduled full revision: 176.

On resumption, first confirm the actual process state and inspect Git
updates. The next proof task is to connect the checked pair/triple logic
to the existing cube and square definitions, preserving all selected-degree
and endpoint hypotheses. Existing sources include work/spectral/SquareIncidence.lean,
work/final_lean/CubeLocal.lean, and the milestone 73 bridge's CoreShareBudget.
The native zero-loss examples show why degree and endpoint conditions
alone, or acyclicity alone, cannot establish a positive loss bound.

A further mathematical target is a restriction coupling domination with
the exact degree-five residue table and the length-at-least 235 hypothesis.
Domination on its own is insufficient. Any numerical search must keep
connectedness, inducedness, and the two-endpoint condition explicit.

The core-only Lean checks use a separate resource profile: 1 GiB startup,
768 MiB free reserve and 256 MiB sampled compiler-private cap. An initial
startup gate stopped before compilation; the later run passed. The large
replay's original 2 GiB startup gate and other resource limits were unchanged.
Historical completion files pin the bytes at their publication commits;
the new paper supersedes the earlier paper hashes without altering those
historical records. The editor file and repository mirror agree.
