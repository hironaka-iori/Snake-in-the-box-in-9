# Research update: milestone 135

A complete theorem for actual snakes has passed Lean: at most thirty-two
fitting canonical 012032 windows can have relevant pair sum at most nine.
The starts are counted once each; windows may overlap, and no path-length
parity assumption is imposed. The proof assigns windows through the checked
common-neighbour property and bounds each endpoint group by sixteen.

The proof includes endpoint normalization, parity and injective reindexing,
separation of differently labelled windows, the covered-union capacity, and
the disjoint partition between endpoints. Five modules and seventeen theorem
reports passed. All compiler attempts and exact dependencies are saved.
The sixteen statement uses the unselected common-neighbour assignment; it
does not assert the broader arbitrary Hamming-distance assignment statement.

The missing-degree identities for the stronger written proof also passed,
including the exceptional three-missing-pair count. Twelve per endpoint and
twenty-four in total remain pending. Next: construct maximal intervals and
combine their actual run-length bounds, degree sums and boundary conventions.

This occurrence theorem alone gives no new upper bound on snake length.
The fixed uniform-credit limitation from milestone 132 still applies.
The recorded interval remains 191–235, with incomplete independent rebuilding
of the contributor upper proof. Optimality and 196 remain open. The paper
remains at revision 126 and is due for its next full revision at milestone 136.
Ordinary notation is retained; no new named mathematical definitions are added.

## Earlier record

# Research update: milestone 134

The geometric steps behind the endpoint occurrence argument have passed Lean.
A canonical 012032 window whose relevant pair sum is at most nine has four
alternate vertices and one endpoint adjacent to a single unselected vertex.
One normalization is valid for every window assigned to the same endpoint.
Apart from path indices zero and two, the relevant vertices are coordinate
pairs among the eight coordinates different from the first path direction.

Consecutive pairs {a,b}, {a,c} force the intervening triple {a,b,c} and exclude
{b,c} from the entire snake. An actual represented sequence of such pairs has
distinct other coordinates and missing opposite pairs between consecutive
entries. The finite pair count and the corresponding simple-list length
bound have also passed Lean. All successful receipts and failed attempts are
saved, with exact source and dependency hashes.

The full occurrence theorem remains pending. Its proposed limits of twelve
windows per endpoint, eleven without a counted boundary window, and twenty-four
in total remain written bounds whose complete actual-snake Lean proof is
unfinished. Next: construct maximal intervals, check their overlap and boundary
conventions, sum missing degrees, and combine with the checked integer reduction.

No new global upper bound is claimed. The recorded interval remains 191–235,
with the documented incomplete independent rebuild of the contributor upper
proof. Optimality and 196 remain open. Paper revision 126 is unchanged; the
next full revision is due at 136. Ordinary notation is retained, with no new
named mathematical definitions in this round.

## Earlier record

# Research update: milestone 133

Two concrete counterexamples have passed Lean. A 149-edge odd snake attains
pair counts 6 and 3 in a canonical 012032 window. A 133-edge odd snake attains
counts 4 and 5. Thus the pair floor cannot be raised uniformly to ten, even
when both counts are at least four. These are auxiliary sharpness examples,
not improvements on the 191-edge construction or realizations of a full
periodic critical cycle. Neither example decides a length 235-only restriction.

The first witness's window starts 130 edges after its qualifying endpoint.
The second is 106 edges from its qualifying final endpoint. Hamming proximity
therefore cannot be replaced by a short distance along the path.

A written geometric argument bounds the number of assigned windows at one
endpoint by twelve, or eleven when no counted window includes that endpoint.
It uses the common coordinate in the alternating window vertices and the
absence of the opposite pair between consecutive such vertices. The interval
packing lemma and final conditional arithmetic have passed Lean. The transfer
from an actual snake to the full geometric counting argument remains pending;
the occurrence theorem itself is not yet Lean-checked.

The endpoint 0 search returned native UNSAT with no cycle cuts. Its exclusion
has no checked certificate and must not be used as a theorem. The other two
searches produced the fully checked witnesses. All inputs, models, valid cuts,
native reviews, compiler attempts and successful receipts are retained.

Next selected task: complete the actual-snake geometric occurrence proof.
Do not replace it by another uniform pair-floor proposal. The recorded global
interval remains 191–235 with the existing incomplete independent upper-proof
rebuild; the optimum and 196 remain open. Paper revision 126 remains unchanged,
with the next full revision due at 136. Only notation needed repeatedly in
the counting proof is introduced.

## Earlier record

# Research update: milestone 132

A new local theorem has passed the complete Lean check. In any snake in Q9,
a fitting canonical 012032 window with second-plus-fourth internal count at
most nine forces one endpoint to be at Hamming distance two from both counted
centres. There is no length-parity assumption. Consequently the pair sum is
at least ten whenever neither endpoint has those two distances.

The proof includes all 51 certificate modules, the interpretation of all 683
selected clauses for an actual snake, and the final coordinate transfer.
It preserves the 42 corner occurrences, including five vertices counted twice.
The final statements use only the standard Lean axioms recorded in their logs.
The two failed semantic attempts and the successful checks are saved.

This is an unconditional local result. It supplies no new global upper bound.
The maintained interval remains 191–235, with the documented incomplete
independent rebuild of the contributor upper-bound proof. The optimum and
the proposed value 196 remain unresolved.

A separate Lean-checked arithmetic result limits the current uniform-credit
approach. The two surviving cycle constraints keep its comparison above 235
when the endpoint-event allowance is at least two. This limitation concerns
the stated fixed model and formula. It does not rule out sharper geometric
restrictions or a revised graph that excludes other surviving cycles.

Next: use the endpoint theorem to study how low-pair windows can occur along
one actual snake. The earlier bound of thirteen windows requires proximity
to BOTH endpoints and cannot be reused for this one-endpoint conclusion.
Retain the seven-edge competing cycle when testing any proposed improvement.
No new mathematical definition is introduced. Paper revision 126 is unchanged;
the next scheduled full paper revision is136.

## Earlier record

# Research update: milestone 131

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

## Earlier record

# Research update: milestone 130

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

## Earlier record

# Research update: milestone 129

The fourth-count-three case of the 0120324 window now has a complete native
contradiction, independently replayed through all 50082 deductions. Its
3500 selected clauses use fewer hypotheses than the original search, supporting
the candidate implication

$$
\alpha_{r+4}=3\quad\Longrightarrow\quad
\alpha_{r+3}+\alpha_{r+5}+\alpha_{r+6}\ge12.
$$

Lean checks the exhaustive case split, the actual-snake count conversions,
and satisfaction of all 3500 clauses under the contrary hypotheses. It also
checks the triple lower bound and the equality-case six-count lower bound 23
conditional on the contradiction of this exact input. These four modules
have 17 successful axiom reports. The complete 221-module Lean refutation is
still running. The candidate implication therefore remains unproved without
that remaining premise. See milestone 129's mathematical note and verification
record for the exact saved progress.

The earlier endpoint batch has also completed. An independent audit verifies
all 448 modules and 30 axiom reports. For a fitting canonical 012032 window,
equality of the second and fourth counts' sum to eight forces both centres
to have Hamming distance two from both endpoints. There are at most thirteen
such starts in any snake. The final theorem has no remaining local-certificate
premise. This occurrence bound needs a further global argument before it
can improve the upper bound on snake length.

The complementary fourth-count-at-least-four case remains unresolved. No
universal six-count bound or improved global upper bound is claimed. The
maintained interval remains 191–235, with the documented independent-rebuild
limitation on the contributor upper-bound proof. The optimum and 196 remain
open. No new mathematical definition is introduced. Paper revision 126 is
unchanged; the next scheduled full revision is 136.

## Earlier record

# Research update: milestone 128

The proved 012032 pair inequality is now connected in Lean to the concrete
0120324 search: at most 34 of its 42 paired corner occurrences are selected.
Five repeated vertices retain both occurrences. Lean also checks satisfaction
of all 2863 added counter clauses for actual snakes. Two modules and ten
dependency reports passed. The conjunction with the preceding 101666 clauses
and a complete contradiction remain separate requirements.

An independent audit reconstructs the new input exactly, and a separate
parser matches the Lean certificate data to the added clauses. The bounded
search timed out after 180.062 seconds, using 24.59375 seconds of process CPU
time. Its first 1000 deductions pass a check against the new input; no complete
refutation or new count floor is established. The partial trace is saved in
a verified lossless archive.

The next selected task splits the fourth count into equality to three and
at least four. In the equality case, existing results force the first count
to be at least three and the second at least five, leaving at most eleven
for the other three counts under the total-22 hypothesis. The split assembly
is written but not yet checked in Lean; neither branch has been excluded.
See `milestones/128-coupled-pair/data/next-case-task.json`.

The maintained range remains 191–235 with the documented independent-rebuild
limitation. The optimum, 196, and the hypotheses for 234/233 remain open.
No new mathematical definition is introduced. Paper revision 126 is unchanged;
the next scheduled full revision is 136.

## Earlier record

# Research update: milestone 127

The direct-clause representation of the existing lower count bounds is checked.
One Lean module proves five generic counting statements. An independent replay
derives all 235 concrete clauses from the original 106348 inputs using 132921
ordered references. No new definition or six-count floor is introduced.

Replacing six lower counters removes 4917 clauses and makes 2457 auxiliary
variables unused. The reduced input has 101666 clauses and 4820 occurring
variables, with exact input mapping for later proof transport. Both changed
encodings timed out after 180 seconds; neither returned a model or contradiction.
The first 1000 native deductions of each trace passed bounded original-input
replay. This does not verify a complete contradiction. Partial traces are
preserved locally and in lossless gzip archives.

The maintained range remains 191–235 with the documented independent-rebuild
limitation. The optimum, 196, and the needed conditions for 234/233 remain open.
Paper revision 126 is unchanged; the next full revision is 136.

The next focused task is to expose the proved second/fourth pair sum at least
eight in the 0120324 encoding. It uses 42 corner occurrences over 37 vertices;
the equivalent selected-occurrence cap is 34. The new counter and its semantic
connection are not implemented. See
`milestones/127-direct-cardinality/data/next-pair-task.json`.

## Earlier record

# Research update: milestone 126

The manuscript is revised through milestone 125. The direct six-count and
empty-square argument now precedes the long graph construction. No new
definition is added, and temporary joint-budget aliases are removed.
The authors and complete local hyperlink settings are preserved.

The paper distinguishes the proved 0123041 six-count bound, sharp 012032
pair theorem and necessary 0120324 intervals from the unresolved universal
floors and shortfall assumptions needed for 234 or 233. Twenty reference
entries are discharged; 1358 and the five additional share targets remain.
The maintained range is 191–235, with its documented independent-rebuild
limitation. Neither the optimum nor 196 is established.

All 16 printed snakes pass 148857 pair checks. Exact evidence from 188 prior
Lean modules and 139 dependency reports is rechecked; there is no new Lean
compilation this round. The built-in PDF compiler failed in its Windows helper
before processing TeX. The source checks pass; PDF compilation and layout
remain unverified. The next scheduled full paper revision is 136.

See milestone 126's README, manuscript verification and reviews. The next
research task remains the unimplemented 0120324 encoding proposal saved in
milestone 125. Inspect the live 104/115/122 drivers before resuming any job.

## Earlier record

# Research update: milestone 125

Retaining empty squares strengthens the checked six-count criterion. Any snake
with at least 235 edges must have total shortfall below 25, across the first
39 disjoint groups of six internal counts, at least 29 + 2s0. A proved upper
bound of 28 + 2s0 on that sum would therefore imply length at most 234.

Two weaker local hypotheses also have checked consequences: universal six-count
floor 24 with at least six empty squares gives 234, and floor 23 with at least
25 empty squares gives 234. Universal floor 25 with at least 14 empty squares
gives 233. The empty-square conditions apply at the lengths being excluded;
all these additional hypotheses remain unproved.

For an actual 0120324 window whose total is at most 22, Lean proves the count
intervals [1,21], [2,21], [1,21], [3,21], [1,21], [1,21]. This is a necessary
restriction on a possible counterexample. Three complete-cube searches timed
out, including the one using these intervals. No new count floor or improved
unconditional global bound is claimed. The maintained range remains 191–235
with its documented independent-rebuild limitation; the optimum and 196 remain
unresolved. Three Lean modules and 19 dependency reports passed.

See [the mathematical note](125-critical-six-count/MATHEMATICAL_NOTE.md),
[proof review](125-critical-six-count/audit/proof-review.md), and
[proof supplement](125-critical-six-count/audit/proof-supplement.md).
The next full paper revision is due at milestone 126. A proposed cardinality
encoding improvement is saved with exact proof obligations; it is untested.

## Earlier record

# Research update: milestone 124

Lean proves that the six internal singleton-square counts sum to at least 25
for direction pattern 0123041 in either orientation, in an actual snake.
This closes one of the 21 reversal classes. There are 46 checked modules and
22 printed dependency reports in the round.

The universal six-count floor 25 would give length at most 234; floor 26 would
give at most 233. Lean checks these implications for actual snakes. It also
checks a weaker sufficient condition for 234: total shortfall below 25 is at
most 28 across 39 disjoint six-count groups. These additional assumptions remain
unproved. The existing notation is sufficient; no new definition is introduced.

The full-cube screen gives 19 negative classes, including the checked class.
The other 18 need checked contradiction proofs. Classes 0120310 and 0120324
remain unresolved. The three-pattern graph experiment cannot improve the
235/234 integer comparisons because attaining cycles avoid all three patterns.
The maintained range remains 191–235 with its documented independent-rebuild
limitation. Neither the optimum nor 196 is established.

See [the mathematical note](124-six-count-cycle-pressure/MATHEMATICAL_NOTE.md),
[proof review](124-six-count-cycle-pressure/audit/proof-review.md), and
[coverage review](124-six-count-cycle-pressure/audit/coverage-review.md).
Paper revision 116 is unchanged; the next full revision is 126.
The next priority is resolving 0120310 and 0120324 or proving the stated
39-group shortfall bound. The older 104, 115 and 122 batches remain separate.

## Earlier record

# Research update: milestone 123

The six-count work gives checked overlap accounting and a new unproved candidate:
the six internal counts sum to at least 26 on the seven-direction pattern
0123042. Two negative full-cube searches support it; no contradiction certificate
or actual-snake transfer has been completed for this candidate.

Neither the recovered exact-six-fours exclusion nor the tested sum credits
improve the integer comparisons. Replacement cycles avoid 0123042 entirely.
The next focused targets are 0120310 and 0123024, with recorded six-count sum 24.
The maintained interval remains 191–235, with its existing independent-rebuild
limitation; 234 remains conditional. No new mathematical definitions were added.

See [mathematical note](123-six-count-recovery/MATHEMATICAL_NOTE.md),
[proof review](123-six-count-recovery/audit/proof-review.md), and
[graph obstruction](123-six-count-recovery/audit/six-sum-guarded-review.md).
Paper revision 116 is unchanged; the next full revision is 126.

## Earlier record

# Research update: milestone 122

The arbitrary-snake endpoint restriction for the 012032 count pair (2,6) is
Lean checked. The conditional equality assembly and geometric occurrence limit
13 are checked; the (3,5)/(4,4) certificates and unconditional equality conclusion
remain in a 381-module batch. The endpoint credit cannot improve the current
integer comparisons: an all-four three-cycle survives even deletion of every
eligible equality event. The maintained interval remains 191–235, with the existing
independent-rebuild limitation; conditional 234 remains unresolved.

See [mathematical note](122-endpoint-equality/MATHEMATICAL_NOTE.md),
[proof review](122-endpoint-equality/audit/proof-review.md), and
[graph review](122-endpoint-equality/audit/endpoint-graph-review.md).
The next numerical target is the three all-four keys in
`milestones/122-endpoint-equality/data/next-six-four-cases.json`; inspect existing
seven-count coverage before searching. Paper revision 116 is unchanged; revise at 126.

## Earlier record

# Research milestones

The exact optimum remains unresolved. The contributor-checked interval is 191 <= a(9) <= 235 edges. Milestones 73 and 80 check four of nine count-free shares, actual-snake catalogue coverage, canonical dispatch and global share accounting. The combined catalogue theorem retains five local certificate premises; 234 remains conditional on these and the graph assembly. The manuscript is at revision 116; the next full revision is 126. Source and witness checks pass; the built-in compiler failed before TeX processing.

- [Milestone 121: a sharp pair bound and an endpoint hypothesis](121-replacement-window-pressure/README.md). Lean-checked pair sum 8, three complete attaining snakes and five catalogue consequences; endpoint necessity remains a candidate, numerical bounds unchanged.

- [Milestone 120: a checked restriction on four outer counts](120-nine-transition-window/README.md). Lean checks the local theorem and three catalogue consequences; 63 additional graph removals, 1,363 reference entries pending, no numerical bound improvement.

- [Milestone 119: actual counterexamples and full-cube count restrictions](119-shared-five-count-pressure/README.md). Lean-checked length148 counterexample, two replayed native contradictions and oriented graph audit; no new numerical bound.

- [Milestone 118: local counterexamples and limits of total-count pressure](118-shared-cycle-outer-sum/README.md). Ten audited local witnesses, two Lean-checked critical forests and fixed-family ceilings; no new numerical bound.

- [Milestone 117: count-sum refinement on both surviving cycles](117-cycle-sum-refinement/README.md). Replayed native contradiction; conditional Lean transfer; finite mean 2915/6; integer comparisons unchanged.

- [Milestone 116: manuscript revision with count-sum results](116-paper-revision/README.md). No new definitions; exact source and witness checks; conditional graph limits; both proof batches preserved.

- [Milestone 115: concrete count semantics and distinct-direction windows](115-total-count-certificate/README.md). Checked semantics, running Lean contradiction batch, a local total23 candidate and improved finite means; no new integer bound.

- [Milestone 114: total-count pressure and native proof replay](114-total-count-pressure/README.md). Independently replayed contradiction, checked conditional geometry and comparison arithmetic; finite mean improves to 484.8, with integer comparisons unchanged.

- [Milestone 113: pair-count restriction and local limitations](113-all-four-sum-pressure/README.md). Checked shared pair budget and conditional geometry; locally sharp native candidate removes 41,361 more keys. Comparison integers remain 235 and 234.

- [Milestone 112: actual sum theorem and shared budget](112-critical-sum-refinement/README.md). Checked geometry and counter semantics; completed finite mean 484 with an exact coefficient ceiling. Integer comparisons remain 235 and 234.

- [Milestone 111: three-count restriction and sum family](111-critical-count-intervals/README.md). A checked local theorem and a conditional fractional graph improvement; integer comparisons remain 235 and 234.

- [Milestone 110: critical-cycle count exclusion](110-critical-cycle-core-screen/README.md). One new actual-snake theorem removes 865 additional keys. Even all seven candidate exclusions preserve both numerical comparisons.

- [Milestone 109: actual-snake restriction and graph test](109-relaxed-graph-test/README.md). A checked restriction excludes 2,092 keys; both profile bounds and five floor obstructions survive. Twelve reference entries checked, 1,366 remaining.

- [Milestone 108: relaxed exclusion and eight recovered entries](108-smaller-reference-recovery/README.md). One smaller contradiction covers seven exact keys; Lean checks the 1,370-entry remaining obligation.

- [Milestone 107: first recovered reference refutation](107-reference-refutation-recovery/README.md). Exact input, regenerated LRAT, closed Lean entry and remaining-list equivalence; 1,377 entries remain.

- [Milestone 106: manuscript revision and precise remaining assumptions](106-paper-revision/README.md). Fewer named definitions; checked graph and weight chain; conditional floor 18; PDF compiler unavailable.

- [Milestone 105: exact reference-proof obligation](105-reference-proof-closure/README.md). Five checked implications using the exact union; closed refutations remain pending.

- [Milestone 104: complete potential batch](104-complete-potential-batch/README.md). Active sequential certification; general graph assembly checked, full graph results pending.

- [Milestone 103: joint potential traversal](103-joint-potential-traversal/README.md). General soundness and four matched comparisons; complete graph certification is next.

- [Milestone 102: bounded potential-block reduction](102-potential-block-reduction/README.md). All 412 fixed block equations and eight new finite profile/context checks; six complete contexts per profile.

- [Milestone 101: exact equations for all contexts](101-context-specialization/README.md). All 791 evaluator equations and two finite contexts per profile checked; complete graph certificates remain pending.

- [Milestone 100: prefix traversal and complete context certificates](100-prefix-potential-checker/README.md). Exact evaluator reductions and two full Lean context checks; all-context certification remains pending.

- [Milestone 99: defined-graph potential checks and concrete ranges](99-defined-potential-certificates/README.md). Full numerical edge audit, checked potential candidates and finite Lean certificates; complete graph certificates remain pending.

- [Milestone 98: actual weights, total charge and conditional bound assembly](98-concrete-weight-integration/README.md). Both floor profiles are integrated with the full edge key; potential certificates, reference closures and five conditional shares remain.

- [Milestone 97: geometric credit integration and least pending floors](97-geometric-credit-integration/README.md). Complete 505-shape geometric/history credit; checked symbol transfers; sharp conditional floor vector (16,18,16,16,16) in the original integer target box. No new global bound.

- [Milestone 96: paper revision](96-paper-revision/README.md). Four statements, complete 55-rule history catalogue, all prior statements and metadata preserved, zero new named definitions. Source checks pass; preview unavailable before compilation.

- [Milestone 95: concrete history-credit integration](95-history-credit-integration/README.md). All 69 geometric and eight capped word bounds, 55 concrete rules and their maximum for actual snakes; 923 theorem audits including the ported source closure. No new numerical bound.

- [Milestone 94: complete history-share configurations](94-history-share-dispatch/README.md). 73 Lean audits; all 55 signatures, 69 exact compatible words, actual-window and capped dispatch. Existing local credits are mapped; compatible concrete instantiation and maximum dispatch remain. No new numerical bound.

- [Milestone 93: joint slope and range comparison](93-defined-graph-potential/README.md). Seven new Lean audits; exact independent certificates show that all three fixed weighted graphs already attain their best constant-slope/global-range comparisons. No new snake bound. Case7302 stopped after a timeout; witness and geometry batches continue.

- [Milestone 92: context assignment and full witness batch](92-full-witness-batch/README.md). All 37,875 context positions checked; 3/127 witness classes at snapshot; complete sequential run active.

- [Milestone 91: certified reference-pattern reuse](91-reference-shape-reuse/README.md). Eight new Lean audits; complete same-case cache pilot; no consistent timing advantage. Use direct checks for the full witness batch.

- [Milestone 90: witness compatibility and counts](90-context-witness-certificates/README.md). 17 Lean audits; six-direction membership pilot, exact lookup tables and generic factorization; 507 base jobs plus three history heads planned. No new bound.

- [Milestone 89: shared-cover checkpoint](89-shared-cover-certification/README.md). 28 Lean audits; balanced geometric classes 0/1 checked, full batch active; all 791 context witnesses materialized computationally. History transport and lookup equivalences checked; no new numerical bound.

- [Milestone 88: rejection boxes and a checked coverage pilot](88-retention-diagram-certificate/README.md). 26 Lean theorem audits; generic rejection/coverage chain and direction-0/history-0 certificate. All 127 common covers are computationally exact; all-context certification and saved-row identification remain open. Bounds unchanged.

- [Milestone 87: retention covers and saved-edge indexing](87-retained-array-membership/README.md). 27 Lean theorem audits; actual numeric acceptance and conditional whole-walk indexing; exact computational coverage of 36,904,896 compatible keys. Concrete Lean finite certificates remain open; bounds unchanged.

- [Milestone 86: revised paper and precise proof scope](86-paper-revision/README.md). 130 statements, fourteen new Lean checks, all 13 printed paths rechecked; five target shares and global assembly remain pending. Editor compilation failed before source processing.

- [Milestone 85: exact reference catalogue union](85-reference-catalogue-union/README.md). 103 Lean audits connect all 1,378 reference keys to the source catalogues and prove retention under their two explicit refutation premises. The exact isolated filter agrees on 23,561,280 pairs. No numerical bound changes.

- [Milestone 84: three-history retention](84-history-exclusion-retention/README.md). 38 Lean audits prove that every actual snake survives all three history guards; complete signature realization and encoded count transport are checked. No numerical bound changes.

- [Milestone 83: 012034 share-20 certificate in progress](83-012034-share-certificate/README.md). 127 semantic modules checked; local refutation replay and final theorem pending. Exact single-target conditional mean 9259/19 still gives integer comparison 235.

- [Milestone 82: obstruction from counts below six](82-unsaturated-cycle-obstruction/README.md). Six Lean audits and exact array checks rule out a class of excess-only bonuses on the current graph; two pending share targets act on the saved cycle. No global bound changes.

- [Milestone 81: forty recovered short-rule filters](81-recovered-short-rule-retention/README.md). 66 Lean audits close this retention family; the exact isolated builder loop agrees on 23,561,280 pairs. Full graph membership and the numerical bounds are unchanged.

- [Milestone 80: 012310 share closure and comparison](80-012310-share-closure/README.md). Case 7305 checked; five local targets remain; proof-supported mean 483 and range 551 still give integer comparison 235.

- [Milestone 79: encoded guards and ten interval exclusions](79-retained-edge-guards/README.md). 31 Lean audits; actual snakes survive the ten completed interval filters. Full graph membership remains.

- [Milestone 78: numeric history transitions and actual state sequence](78-numeric-history-transition/README.md). 29 Lean audits; retained-edge membership and charge interpretation remain.

- [Milestone 77: actual direction states and history compatibility](77-direction-state-coverage/README.md). 106 Lean theorem audits; complete retained-edge interpretation and the target234 remain pending.

- [Milestone 76: paper revision and conditional arithmetic](76-paper-revision/README.md). Seven statements added, six fresh Lean checks; no new unconditional bound.

- [Milestone 75: exact history, share lookup and count-state coding](75-exact-history-bridge/README.md). 39 Lean audits; selected case7305 replay in progress; full graph interpretation and234 remain pending.

- [Milestone 74: exact graph interpretation audit and short-walk obstruction](74-graph-interpretation-audit/README.md). Five new Lean audits; six verified finite-graph witnesses; pending case7305 proof compressed and preserved. See the [current handover](../handoff/2026-11-02/START_HERE.md).

- [Milestone 73: count-free catalogue and global accounting](73-countfree-share-catalogue/README.md)

- [Milestone 72: short-count proof closure (in progress)](72-four-count-proof-closure/README.md)

- [Milestone 71: reduce conditional proof obligations using proved rules](71-proved-rule-conditional-pressure/README.md)

- [Milestone 70: proof-supported comparison and recovered restrictions](70-proof-supported-share-model/README.md)

- [Milestone 69: select count exclusions for the target bound](69-count-certificate-selection/README.md)

- [Milestone 68: remove numerical-only share premises](68-proof-dependency-pressure/README.md)

- [Milestone 67: critical-family charge and improved boundary accounting](67-critical-family-charge/README.md)
- [Milestone 66: complete-model integration and manuscript revision](66-full-model-and-revision/README.md)
- [Milestone 65: count saturation and forced share](65-count-saturation-share/README.md)

- [Milestone 64: complete neighbour-choice share bounds](64-neighbour-choice-share/README.md)

- [Milestone 63: vertex splits on eleven-transition windows](63-long-window-splits/README.md)

- [Milestone 62: empty-square share under a vertex case split](62-count-conditioned-share/README.md)
- [Milestone 61: empty-square charge on the complete critical family](61-critical-family-share/README.md)
- [Milestone 60: extending the recorded critical cycle](60-critical-window-extension/README.md)
- [Milestone 59: extending the forced-empty-square window](59-extended-share-window/README.md)
- [Milestone 58: forced-absence share bounds](58-share-pressure/README.md)
- [Milestone 57: share candidates covering the replacement family](57-replacement-share-family/README.md)
- [Milestone 56: zero-credit packing limitation and paper revision](56-packing-limit-and-revision/README.md)
- [Milestone 55: share constraints across the critical family](55-critical-share-family/README.md)
- [Milestone 54: coverage of the empty-square share inequalities](54-share-coverage/README.md)
- [Milestone 53: empty-square shares on a satisfiable obstruction](53-shares-on-sat-obstruction/README.md)
- [Milestone 52: empty-square shares against the 235 baseline](52-share-on-235/README.md)
- [Milestone 51: empty-square shares on critical windows](51-exact-bucket-pressure/README.md)
- [Milestone 50: a sharp triple inequality and targeted range optimisation](50-three-count-return/README.md)
- [Complete survey of low two-count restrictions on six-direction segments](49-six-direction-pair-catalogue/README.md)
- [Low-count compatibility in short snake segments](48-low-count-compatibility/README.md)

- [Three transition-pattern singleton restrictions](47-critical-singleton-patterns/README.md)
- [Sharp pair endpoint demand](45-pair-endpoint-demand/README.md)
- [Manuscript revision after the endpoint theorem](46-endpoint-paper-rewrite/README.md)

- [Foundations, witnesses, and numerical hypotheses](01-foundations/README.md)
- [Layer constructions](02-layer-constructions/README.md)
- [Square incidence and the 254 bound](03-square-incidence/README.md)
- [Singleton geometry and counterexamples](04-singleton-geometry/README.md)
- [Unconditional upper bound 245](05-upper-bound-245/README.md)
- [Radius-five Boolean obstruction](06-radius-five/README.md)
- [Three-center pattern(2,2,3)](07-window-223/README.md)
- [Exhaustive search and regrowth certificates](08-exhaustive-search/README.md)
- [Method limits and endpoint accounting](09-research-directions/README.md)
- [Window exclusions and conditional bounds 242/241](10-window-aggregate/README.md)
- [Constructive search targeting 196 edges](12-construction-196/README.md)
- [Diverse walks and solver-guided repair](13-diverse-construction/README.md)
- [Construction through a path and cyclic components](14-component-construction/README.md)
- [Targeted mergers and frozen-cycle accounting](15-component-mergers/README.md)
- [Larger cycle configurations and local cell states](16-cycle-reservoirs/README.md)

Active direction as of 23 October: milestone 31 proves joint singleton-count excess and its weighted contribution to the empty-square charge (20 Lean audits). Milestone 32 tests a direction-independent prohibition on six consecutive count-four centres; all 34 cases are solver-excluded and finite coverage is checked, but the complete theorem is pending. The global bound is unchanged.

The relocation manifest records moved files. Historical proof logs and source-hash manifests retain their original recorded paths as provenance.

- [Expanded cells](18-expanded-cells/README.md)
- [Coordinate-face repair](19-coordinate-face-repair/README.md)
- [Middle-path release](20-middle-path-release/README.md)
- [Endpoint recombination](21-endpoint-recombination/README.md)
- [Internal-anchor donors](22-internal-anchor-donors/README.md)
- [Parity-compatible face searches](23-parity-compatible-faces/README.md)
- [Contracted fixed-path search](24-contracted-face-search/README.md)

- [Alternative fillings and retained changes](25-alternative-fillings/README.md)
- [Global cell construction](17-global-cell-construction/README.md)
- [Empty-square shares and weighted window packing](27-empty-square-packing/README.md)

- [Direct share tests and checked window exclusions](28-direct-share-certificates/README.md)
- [Overlapping share windows and selective history](29-overlapping-share-windows/README.md)

- [Coarse singleton-count correction](30-coarse-count-correction/README.md)

- [Joint singleton-count bounds](31-joint-counter-soundness/README.md)
- [Consecutive singleton counts equal to four](32-seven-count-four-screen/README.md)

- [Distance-three singleton inequalities](33-distance-three-singletons/README.md)

- [Sharpness of the distance-three inequalities](34-distance-three-sharpness/README.md)

- [Three-square empty-share bonus and occurrence accounting](35-equality-share-bonus/README.md)

- [Joint consistency of critical cycles](36-critical-cycle-consistency/README.md)

- [Logical manuscript rewrite and verification](37-logical-paper-rewrite/README.md)

- [Asymmetric restrictions at Hamming distance four](38-four-position-obstruction/README.md)

- [39: Audited radius-four bound of 236](39-audited-bound-236/README.md): pinned contributor theorem, complete exclusion catalogue, independent potential checks, four new Lean arithmetic checks, and revised manuscript proof.

- [40: Intervening-count restrictions](40-intervening-counts/README.md): two new three-position implications, eight Lean audits, 23 checked local forests, a saved cyclic relaxation, and exclusion of the identified low-mean cycle occurrence.

- [41: Joint intervening-count bound and excess accounting](41-joint-intervening-sum/README.md): sum12 theorem, ten Lean audits, conditional charge contribution, and full published-bank controls.
