# Milestone 131: the full comparison and its remaining cycles

The full graph comparison has completed. Adding the proved odd-length pair
bound nine and the proposed 0123104 six-count bound twenty-five raises the
first profile's minimum from 2915/6 to 488. Its integer comparison remains
235. The additional-share profile retains minimum 496 and its previous
integer comparison 234. Both profiles still contain unproved hypotheses;
these are finite-model comparisons, with no new bound for actual snakes.

The new attaining cycles avoid 0123104. Raising only that proposed bound
above twenty-five therefore cannot improve either minimum in this model.
The existing potentials remain valid as weights increase or edges disappear,
and the same unaffected cycles attain equality. Even zero potential range
would leave the comparisons above 235 and 234, respectively. This rules out
further progress toward 234/233 by strengthening only that pattern.

The first profile's four-edge cycle consists entirely of 0120324 windows
up to reversal, with relevant pair sums exactly nine. This identifies the
next question: for an odd-length snake, does a fitting 012032 window with
pair sum nine force one endpoint to be at Hamming distance two from both
counted centres? This is a hypothesis. A screen of 133 validated saved snakes
found 54 relevant windows and no pair-sum-nine window, so it gives no evidence
for or against the hypothesis.

The evaluator checked every retained-edge potential inequality; the
independent review reconstructed the saved cycles from original graph rows
and checked their weights, adjacency and zero slacks. It did not repeat the
full all-edge calculation. No new Lean theorem is claimed in this round.
The next selected task is a direct counterexample search for the odd-length
endpoint statement, followed by a checked certificate if the search is negative.

The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. The optimum and
196 remain open. Existing notation is retained. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

## Saved evidence

- MATHEMATICAL_NOTE.md gives the numerical comparisons and the next hypothesis.
- data/odd-pair9-six25/results.json records the exact finite-model results.
- The same directory contains both potentials, cycles, source snapshot and logs.
- audit/graph-review.md distinguishes the evaluator's all-edge check from the
  independent reconstruction of the saved cycles.
- audit/endpoint9-witness-screen.md records the vacuous saved-witness screen.
- data/next-endpoint-task.json specifies the selected counterexample query.
- data/batch-observation.json records the other proof jobs at checkpoint time.
- data/verification.json, data/checkpoint.json and data/file-manifest.json
  identify the exact saved scope and bytes.

The historical preparation and low-memory observation remain unchanged. The
later launch record confirms that both resource gates passed and the full
calculation completed. The transient first GitHub refresh failure was resolved
on retry. A Git commit-graph warning did not prevent retrieval of the pinned
historical graph algorithm.

Do not rerun the completed graph or overwrite the original attempt. Any new
experiment must have a distinct label and preserve the existing evidence.
The milestone 115 proof job is separate and pending; inspect its process and
lock before any restart. Milestone 104 remains stopped after its timeouts.
