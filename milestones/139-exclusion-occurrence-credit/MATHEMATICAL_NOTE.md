# Milestone139: limits of uniform occurrence credit after exclusion

## Result

The exact graph experiment completed on1,601,856 states and4,661,772 retained
edges. The full-nine theorem removed exactly edge992157. Uniform suffix
credit83/3 was applied to8,846 exactly recognized low-pair events. Count
symbols6 were excluded from this event test because they mean at least6.

| Weight profile | Mean | Potential range | Comparison | Attaining cycle |
|---|---:|---:|---:|---:|
| Completed shares |2446/5|2973/5|5520661/23446|5 edges, zero credited events|
| Additional shares |496|602|552097/2348|6 edges, zero credited events|

Both comparisons exceed235. Both profiles retain all milestone131
hypotheses: inherited unproved count-sum claims, the hypothetical0123104
six-count floor25, and the pair floor9 for odd-length snakes. The additional
profile also assumes its share floors. These are conditional finite-model
results, not new actual-snake upper bounds. In particular, an even-length
bound does not follow automatically from this odd-length model.

The evaluator reproduced the immediate predecessor's complete removal set
and both weight hashes, checked every new edge potential inequality and
an attaining cycle for each mean. An independent review reconstructed
40 selected original rows, cycle weights, adjacency and zero potential
slack, and checked source hashes, predecessor counts, potential arrays,
ranges and comparison arithmetic. It did not repeat the all-edge scan.
No full finite-potential Lean certificate was generated this round.

## Checked logic and optimisation limit

Credit139 proves that both clipped counts below6 certify their actual
values, and that distinct suffix starts counted by this condition inject
into milestone137's actual low-pair starts. Therefore this subset also
contains at most24 starts. The result applies to either path parity;
the additional odd-length restriction belongs to the comparison graph.

The new five-cycle receives no credit. Its completed-profile mean therefore
stays2446/5 for every uniform credit C. The old four-cycle has mean488+C/2.
Using these two upper restrictions on the graph mean and allowing any
nonnegative potential range gives

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}
\ge\frac{2757328}{11723}>235.
\]

The arithmetic relaxation attains equality at C=12/5, mu=2446/5, R=0.
This is a proved optimum of the displayed relaxation, not evidence of a
graph potential with zero range or of the best actual credit parameter.

Obstruction139 proves more generally that the five-cycle mean cap prevents
this comparison from reaching235 for any nonnegative credit, allowance
and range. The zero-event six-cycle similarly keeps the additional-profile
mean at most496 and prevents its comparison from reaching234. OptimalCredit139
checks the sharper completed-profile relaxation above.

All three new modules passed Lean, with six axiom reports in total using
only propext, Classical.choice and Quot.sound. The graph means themselves
are supported by exact computation and the saved independent review;
the obstruction theorems explicitly take the relevant mean caps as premises.

## New critical window and selected continuation

The completed five-cycle consists of edges308566,3806548,2195856,163743,
2303753. Its first row has directions012034054 and six counts335453.
Its canonical suffix is012032 with five counts(3,5,4,5,3). The relevant
pair sum is10, so the proved endpoint consequence for pair sum<=9 does
not cover it.

A fresh validation of the same135 distinct saved actual snakes checked
2,447,698 unordered vertex pairs and25,479 internal counts. It found one
full-nine shape occurrence and136 suffix-shape occurrences, but no exact
required count match in either case. Both whole-path orientations were
tested. This supplies no exclusion proof and no counterexample.

NEXT SELECTED TASK: a bounded actual-path feasibility test for the symmetric
six-transition window012032 with exact counts(3,5,4,5,3), beginning with
the necessary full-cube model and ordinary cycle cuts. If it is impossible,
certify the contradiction and its actual-snake interpretation. If an actual
snake realizes it, keep the witness and test a stronger local charge or
endpoint consequence only when the witness permits it. Do not assume the
count pattern forces an endpoint. The original full-nine row is a narrower
fallback if the shorter pattern is feasible.

The pending milestone138 short cap(3,3,3,5,2) has no match on either new
attaining cycle and is not the selected next calculation. Do not launch
a large proof batch solely because that older certificate is available.

## Files and paper

data/exclusion-credit83 holds the exact script snapshot, complete graph
result, both potentials, removed indices and logs. data/result-review.json
and audit/check_result.py hold the independent saved-result review.
The three Lean receipts, exact compiler inputs, outputs and objects are
saved alongside the source. All statuses and hashes are indexed by the
checkpoint manifest.

The existing paper received targeted update139, with unchanged authors and
preamble and no new definitions. Source checks pass. The built-in compiler
again failed before TeX execution; no updated PDF or visual check is claimed.
Last full revision136; next full revision146.

The maintained interval remains191–235 with the documented incomplete
independent upper-proof rebuild. The optimum and196 remain open. The
milestone115 driver was observed live at1056/1397; never duplicate a live job.
The previous goal turn and this round both made concrete progress.
