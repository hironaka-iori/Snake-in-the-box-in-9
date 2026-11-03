# Milestone 130: parity and the fourth-count equality case

Two local inequalities are now proved for actual snakes. For a fitting
canonical direction window 012032 beginning at position r,

$$
\alpha_{r+2}+\alpha_{r+4}=8
\quad\Longrightarrow\quad m\equiv r\equiv0\pmod2.
$$

Consequently the pair sum is at least nine whenever the snake length or the
window start is odd. The proof uses the completed endpoint theorem and the
ordinary parity of cube vertices. No new mathematical definition is introduced.

For a fitting canonical window 0120324, Lean also checks

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

Together with the established first and second count bounds, this gives a
six-count sum of at least 23 in that case. All 221 modules of the exact
contradiction and the final actual-snake application passed. The final
statements have no remaining local-certificate premise. The complementary
case with fourth count at least four remains unresolved: its separate search
timed out without a model or contradiction. Lean checks the meaning of all
717 added clauses for that case, which does not exclude it.

The parity restriction removes the saved four-edge witness for odd-length
snakes. The saved eighteen-edge witness has no matching pair window and
survives. Its most frequent seven-direction shape is 0123104. A proposed
six-count floor 25 for that shape increases this witness's hypothetical mean
from 2915/6 to 3011/6, but the full graph has not been recomputed. The next
selected test is that full comparison, preserving every inherited unproved
hypothesis and combining overlapping credits by their maximum.

The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. No improved global
bound is claimed. The optimum and 196 remain open. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

## Evidence and continuation

- MATHEMATICAL_NOTE.md gives the deductions and their exact scope.
- audit/odd-pair-derivation.md explains the parity result; the module has
  eight checked reports and its rebuilt dependency has four.
- audit/equality-completion-review.md audits the full 221-module refutation
  and the three final actual-snake statements.
- audit/large-review.md and audit/large-derivation.md distinguish the
  complementary search timeout from its checked 717-clause interpretation.
- audit/odd-cycle-review.md checks the two saved cycles only.
- data/next-pressure-task.json records the selected full-graph experiment.
- data/replay129-archives.json and data/replay129-completion-archives.json
  preserve the new proof evidence beyond the previous checkpoint. The first
  records a 199-module intermediate snapshot; the second completes all 221.
- data/trace-archives.json preserves the two incomplete native traces.
- data/batch-observation.json records the other proof jobs at checkpoint time.
- data/checkpoint.json, data/verification.json and data/file-manifest.json
  give the precise saved status and file hashes.

After a fresh checkout, run this milestone's scripts/verify_saved.py
--restore-archives and then --verify. It restores prerequisite archives from
milestone 129 as well as this milestone's archives. Existing evidence
is never overwritten by archive restoration. Inspect the live milestone 115
process and lock before any restart. Milestone 104 stopped after its own
timeouts and has not been resumed. Milestone 129's refutation is complete.

The first native attempt in this milestone was interrupted without a terminal
record. The separate resumed attempt timed out after 300.172 seconds, using
29.546875 seconds of process CPU time. Both incomplete traces are retained
locally and in verified lossless archives. Neither establishes an exclusion.
