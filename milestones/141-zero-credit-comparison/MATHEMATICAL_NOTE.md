# Milestone 141: zero occurrence credit after the local exclusion

The proposed zero-credit test completed on 1,601,856 states and 4,661,572
retained edges. The checked five-count exclusion removed 200 edges from
milestone139. Both previous weight hashes and the entire predecessor
removal set were reproduced before the new rule was applied.

| Profile | Mean | Potential range | Comparison | Integer part |
|---|---:|---:|---:|---:|
| Completed share catalogue |3424/7|4159/7|7724271/32824|235|
| Additional share hypotheses |496|602|551765/2348|234|

The latter fraction equals235-15/2348. This recovers a conditional comparison
with integer part234. It does not improve the unconditional upper bound.
Even the completed-share profile retains inherited count hypotheses;
its name describes the share catalogue, not the status of the full proof.

## Verification and limitations

The evaluator checked every one of4,661,572 potential inequalities in each
profile and a cycle attaining each minimum mean. An independent review
reconstructed221 selected original rows, checked all200 new deletions,
cycle weights/adjacency/slacks, potential hashes/ranges and exact arithmetic.
It streamed original array data in chunks of at most1MiB. It did not repeat
the complete edge-inequality scan or establish minimal potential range.
The old conditional six-cycle survives; the new reported six-cycle is
different and has the same mean496. Both contain no counted event.

Lean checked eight statements: both exact comparisons, their integer
consequences assuming the path-length comparisons, the next credit's
intersection and range threshold, and the two-cycle arithmetic relaxation.
All reports use only propext, Classical.choice and Quot.sound. The finite
potential itself has not received a complete Lean certificate here.

The new local theorem from140 applies to arbitrary snakes and either parity.
The graph still inherits earlier unproved count-sum claims, the hypothetical
0123104 six-count floor25, the odd-length pair floor9, and additional share
floors in the second profile. Complete graph-to-snake assembly and any
required even-length argument remain separate. The maintained interval
191–235 and the unresolved optimum/196 are unchanged. The contributor235
upper proof still lacks a complete independent rebuild.

## Completed-share continuation

The new completed-profile seven-cycle has total weight3424 and two counted
low-pair suffix events. The old18-cycle survives, has no such event, and
has mean3011/6 under the current shared charges. Hence uniform credit C
leaves the two necessary mean restrictions

\[
\mu\le(3424+2C)/7,\qquad\mu\le3011/6.
\]

Their intersection is C=533/12. Under these two caps and nonnegative C,mu,R,
Lean proves the arithmetic lower bound

\[
\frac{1098960+8\mu+24C+R}{4200+\mu}\ge\frac{6624244}{28211}.
\]

Equality in this relaxation occurs at C=533/12,mu=3011/6,R=0. This no longer
prevents a comparison below235. It does not show that the graph has that
mean or admits zero potential range. Other cycles and actual range can
still prevent an improvement.

NEXT SELECTED TEST: use C=533/12 on the completed-share profile. At target
mean3011/6, a comparison below235 is equivalent to R<5341/6. The zero-credit
additional-share result remains the retained comparison for that profile.
There is no need to recompute it at the positive credit merely for symmetry.

Use integer weights12*w+533*event. If their exact mean is p/d and their
integer potential range is R_scaled, the comparison is

\[
\frac{12\cdot1098960d+8p+24\cdot533d+R_{\mathrm{scaled}}}
     {12\cdot4200d+p}.
\]

Actual mean and range divide by12. The target scaled mean is6022 and the
strict target scaled range is10682. Preserve both historical139 weight-hash
checks at their original scale3/credit83; only the new profile weights and
comparison change. Keep all inherited hypotheses and the checked140 gate.

## Saved records

The exact run, two potentials, removed indices and source snapshot are in
data/five-cycle-zero. Bounded independent reviews are in data/result-review.json
and data/zero-credit-source-review.json. The candidate parameter and saved-cycle
checks are in data/next-credit.json; arithmetic proof receipts are separate.
All exact sources and logs are retained. No141 calculation remains running.
The separate115 driver was observed live at1127/1397; inspect its actual
process before any action and never duplicate a live job.

The existing paper received targeted revision141 with no new definitions,
unchanged authors, preamble and hyperlink settings. Both copies match.
Source checks pass. The built-in compiler failed before TeX execution, so
no rebuilt PDF or layout check is claimed. Last full revision136; next146.
This round and the previous round made concrete progress. Goal ACTIVE.
