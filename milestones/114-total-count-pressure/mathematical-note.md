# Total counts on the replacement cycles

This round tests the five-count sum on canonical direction pattern
`012310`. It uses the existing count and charge notation and introduces
no definitions.

## Local restriction

The candidate is

\[
\alpha_{r+1}+\alpha_{r+2}+\alpha_{r+3}
+\alpha_{r+4}+\alpha_{r+5}\geq19
\]

for a fitting six-step window of shape `012310`, without extra count
caps. The radius-four solver reports UNSAT for a total at most 18 in
19.875 seconds, after adding eight verified cycle exclusions. The formula
has 3,129 variables and 55,860 clauses including those exclusions. Its
sum counter contains 105 literal occurrences representing 84 distinct
literals. The repetitions are necessary because one vertex can contribute
to several counts.

Lean checks the geometric transfer from the corresponding local
contradiction to this actual-snake inequality. That contradiction remains
an explicit premise until its concrete certificate and counter semantics
are checked. No actual-snake sum theorem is claimed from the transfer
alone.

A stronger total lower bound of 20 has only an UNKNOWN result after
30.016 seconds and eleven cycle exclusions. That run proves neither
feasibility nor impossibility. The stronger graph experiment below treats
the lower bound of 20 solely as a hypothesis.

## Effect on both graph profiles

The previous eight rules from milestone 113 are retained. The new
five-count rule uses their existing shared charge with balanced
coefficients 24; applicable credits are combined by maximum. No new
budget or separate addition of full credits is introduced.

| Assumed restriction on `012310` | Further keys removed beyond 113 | Remaining keys | Completed mean | Completed range | Conditional mean and range |
| --- | ---: | ---: | --- | --- | --- |
| Total at least 19 | 2,263 | 4,865,603 | \(2424/5\) | \(2881/5\) | 496 and 602 |
| Total at least 20 | 8,030 | 4,859,836 | \(2424/5\) | 565 | 496 and 602 |

The first completed mean improves from 484 to \(2424/5=484.8\).
The stronger hypothesis improves its potential range by \(56/5\)
but leaves the mean unchanged. The exact comparisons are

\[
\frac{5517073}{23424},\qquad
\frac{5517017}{23424}
\]

for the two completed-floor experiments, and
\(551765/2348\) for both conditional-floor experiments. Their integer
parts remain 235 and 234 respectively. The word `completed` identifies
the source of the share floors; both new graph calculations still assume
unproved count restrictions.

The native runs check an integer potential inequality on every retained
edge and save an attaining cycle. An independent audit verifies all 36
saved cycle-edge occurrences, their full direction/history/count keys,
diagram acceptance, endpoints, original weights, potential bytes and
ranges, and exact comparison arithmetic. That independent audit does not
repeat the full-edge scan. Complete Lean graph certification and actual
snake integration remain separate obligations.

Every applicable count deficit vanishes on these cycles, at both eligible
placements. Their weights therefore remain unchanged under any
nonnegative change of the nine rule coefficients. They bound the finite
minimum means above by \(2424/5\) and 496 within this fixed family.
The saved balanced-coefficient potentials attain those values. Further
coefficient changes within this family cannot improve either mean.

## Quantitative requirements for an integer improvement

The existing comparison is

\[
(4200d+p)m\leq1098960d+8p+R,
\]

where \(p/d\) is the graph mean, \(d>0\), and \(R\geq0\) is
the range of the scaled integer potential. Excluding length 235 by this
comparison requires exactly

\[
227p>111960d+R.
\]

Excluding length 234 requires exactly

\[
226p>116160d+R.
\]

Lean checks both equivalences. Thus even a zero potential range would
require means exceeding \(111960/227\) and \(58080/113\), respectively.
The present means remain below those thresholds. Lean also checks that
\(5p\leq2424d\) leaves length 235 compatible with the comparison for
every nonnegative range. Range optimization alone cannot turn the current
completed mean into an upper bound of 234.

## What the replacement cycles show

The completed cycles still contain `012034` and `012310` windows. However,
the conditional cycle under the hypothetical lower bound of 20 uses
suffix shapes `012345`, `012304`, and `012301`, with no suffix of shape
`012034` or `012310`. Strengthening only the latter two suffix rules
cannot change that particular cycle's credit.

The only suffix shape common to all four saved cycles is `012345`.
The completed tuple is \((4,3,3,5,4)\), with total 19. The conditional
cycle under the stronger hypothesis contains \((5,4,2,5,5)\) and
\((5,4,3,4,5)\), both with total 21. Their common condition is a
middle count at most 3 and a total at most 21. This is a useful bounded
test cell; its impossibility is untested in this round. Exact-tuple tests
can distinguish individual exclusions from a broader sum inequality.

## Existing verification batch

The previous complete-potential batch was found stopped. Its final
attempt had a process-termination exit code and an empty compiler log,
so the record supplied no Lean proof diagnostic. One monitored retry
of the unchanged module passed in 175.61 seconds with four standard
axiom reports. The existing driver then resumed from its checked receipts.
The failed attempt and stopped-state snapshot are preserved. No source
repair was made, and previously checked groups are reused only after
their hashes are validated.

## Certificate obtained in this round

A direct proof attempt on the full formula timed out after 60 seconds.
The solver used by the successful probe then produced a complete DRAT
text in 18.343 seconds. A separate checker passed its positive, invalid
and truncated-proof controls, but conversion of that text timed out.
Its partial LRAT output lacks an empty-clause conclusion and is not a
completed certificate.

The conversion did extract 5,431 original input clauses. Every clause
was matched to the original formula, with literal permutations accounted
for, and the original literal order was restored. An attempt on this
subset timed out when writing directly to the research volume. The same
formula and solver options, using system temporary storage for the input
and proof, completed in 20.656 seconds. Its proof begins with exactly
the 40,935,424 bytes saved by the earlier timed-out attempt. The complete
proof was copied back with matching hashes.

After discarding unused deductions, the certificate uses 5,206 original
clauses, 358,464 deductions and 22,088,504 propagation hints. An independent
RUP implementation replayed every deduction, first for the selected
input formula and then after mapping all identifiers back to the full
55,860-clause formula. Both replays derive the empty clause. This is a
completed native contradiction certificate. Its concrete counter
interpretation and full replay in Lean remain pending.

A further trial reused 115 directly validated induced-cycle exclusions,
including the eight original exclusions. Its alternative proof retained
29,534,822 hints, exceeding the selected certificate's 22,088,504. It was
therefore retained as an unselected, unreplayed alternative. More input
restrictions did not shorten the retained proof in this trial.

The next proof task is to reduce the selected certificate before its
Lean export. The existing generic sum-counter semantics preserve all
105 occurrences; replacing them by the 84 distinct literals would change
the mathematical inequality. A later local search can test the recorded
`012345` cells once this proof obligation has been advanced.

## Current scope

The local contradiction has been independently replayed outside Lean.
The geometric transfer and comparison arithmetic pass Lean; a complete
Lean proof of the concrete local inequality is still required. The
maintained interval remains 191 through 235 edges, based on
the contributor proof and archived audit, with a complete independent
rebuild pending. Conditional 234, the optimum and 196 remain unresolved.
Paper revision 106 is unchanged; the next full revision is 116.
