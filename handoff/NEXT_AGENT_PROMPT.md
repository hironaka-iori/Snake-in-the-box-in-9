# Continuation assignment

Continue the empty-square/count-sum route in `E:/Snake-in-a-box`.
Read milestone 113's mathematical note, proof summary, checkpoint and
independent review. Keep the research goal active. Use existing notation;
introduce a definition only when essential and repeatedly used.

## First mathematical test

Test canonical direction pattern `012310` with five unrestricted count
bounds `[0,21]` and total at most 18. The replacement completed cycle
contains `(3,4,5,3,3)` and `(3,3,5,4,3)`; the conditional cycle contains
`(2,4,5,5,2)`. Each sums to 18. A valid total lower bound of 19 would remove
an edge from each saved cycle. Further cycles may preserve the means, so
evaluate a viable inequality on both full profiles before expensive
proof export. This exact total test was not run in milestone 113.

Use a new milestone folder and preserve existing outputs. If the test
produces a model, independently reconstruct all degrees, counts, boundary
conditions and cycles. If it reports UNSAT, retain that status as native
evidence until a concrete contradiction has been replayed and its actual
snake interpretation checked. UNKNOWN provides no impossibility result.

## Current limitations and available proofs

Milestone 113's candidate is: canonical `012034` with central caps `(5,4,5)`
implies outer pair at least 9. Its cap-8 native probe reports UNSAT without
extra cycle cuts. Both CaDiCaL 2.1 proof attempts, default and `--plain`,
time out after 30 seconds. Their distinct CNFs and partial proof files
are saved; do not restart either unchanged merely because it is pending.

`PairGeometry113.actual_pair_sum` passes Lean but retains the local
contradiction premise. It is not a completed concrete pair-sum theorem.
`PairBudget113` passes three arithmetic lemmas: a pair deficit is bounded
by the two excesses, and its weighted maximum with previous credit fits
the existing shared budget. Local lower bounds remain hypotheses.
There are two successful modules, four standard axiom reports and no
new definitions in this round.

The exact local witness `(6,5,4,5,3)` attains pair sum 9 under the caps.
Two more witnesses have counts `(10,4,4,3,6)` and `(5,5,4,5,5)`.
All three have relaxed boundaries and multiple components. They limit
the local model and do not construct complete snakes.

Milestone 112's `ActualSum112.actual_outer_sum` is a complete checked
actual-snake result: canonical `012314`, middle at most 2, outer four sum
at least 19. Its checked sum semantics preserve all repeated literals.
That sum has 84 occurrences and 70 distinct literals. The present pair
sum has 42 occurrences and 41 distinct literals; preserve multiplicity.

## Both graph comparisons

Milestone 113 `data/pair-rules.json` contains the previous seven rules
and the new pair candidate. The graph retains 4,867,866 full keys after
41,361 further deletions beyond milestone 112. Direction, history and
count code must all be retained. Count symbol 6 represents actual counts
6 through 21. A rule applies only when its whole bucket satisfies every
count cap. Reverse count positions when reversing the direction window.

Take the maximum applicable weighted deficit. The generic fixed budget
uses `4*a+b<=120`; pair and outer-four deficits have coefficient `a`,
total-five deficits coefficient `min(a,b)`. Existing share credit is
separate. Balanced coefficients `(24,24)` give mean/range 484/557 in the
completed-floor profile and 496/602 in the conditional-floor profile.
The resulting rational comparisons are `1103389/4684` and `551765/2348`,
with integer floors 235 and 234. Both calculations assume unproved sum
rules. The name `completed` refers only to its share-floor source.

Every applicable count deficit is zero on each saved replacement cycle.
Therefore any nonnegative coefficient changes within this fixed family
leave cycle ceilings 484 and 496. Balanced coefficients attain both.
Milestone 112's checked arithmetic also rules out an integer improvement
from reducing nonnegative potential ranges alone at these mean ceilings.
Do not repeat coefficient sweeps within this family.

## Preserve and verify

Verify milestone 104's live process before interpreting its saved state.
Never restart or modify that active batch. Allow at most one additional
Lean compiler, following the existing memory gate. Keep all immutable
receipts, failed attempts and raw proofs. Run milestone 113's
`scripts/verify_saved.py --verify` against the saved checkpoint. Restore
missing large originals with `--restore-archives` on a fresh checkout.

The original reference union still has 1,366 unresolved entries; twelve
checked indices are `0,472,495,535,572,602,619,620,1006,1010,1011,1014`.
The new pair experiment closes none. Complete graph integration,
orientation guards, remaining local hypotheses and aggregate potential
assembly remain separate proof obligations.

The maintained range remains 191 through 235 edges, with a complete
independent rebuild of upper-bound evidence pending. Conditional 234,
the optimum and 196 remain unresolved. Check GitHub before work and push
a reviewed completed round. Preserve unrelated local edits. Keep paper
revision 106, the three authors and hypersetup; revise the full paper at
round 116 unless the user requests an earlier revision.
