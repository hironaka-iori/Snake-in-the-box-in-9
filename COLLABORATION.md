# Research update: milestone 136

Four Lean modules and eleven theorem reports passed. The checked results
construct blocks of nearby window starts, bound the overlap of their covered
intervals, apply the run-length estimate to actual missing pairs, and count
the available outside coordinates. Maximal intervals in the full snake are
unnecessary for this block construction. No named definition is added.

The complete actual-snake occurrence bound remains sixteen per endpoint and
thirty-two in total under the checked common-neighbour assignment. Twelve
and twenty-four remain pending: the block construction must still be combined
with the boundary count, degree sums and exceptional case. See
`milestones/136-intervals-and-paper/MATHEMATICAL_NOTE.md` for the exact scope.

The paper is now revision 136. The existing editor source and repository copy
match, with all three authors and the complete hyperlink settings preserved.
The final source checks resolve every reference and reconstruct the two new
printed witnesses over 20,086 vertex pairs. The built-in compiler failed
before TeX execution because of a Windows helper restriction; the updated
PDF and its layout remain unverified. The next full paper revision is 146.

The recorded global interval remains 191–235, with incomplete independent
rebuilding of the contributor upper proof. Optimality and 196 are unresolved.
The fixed uniform-credit comparison still cannot lower the length bound
using an occurrence allowance of at least two. Further length improvement
requires its remaining cycle constraint or a stronger comparison.

The saved process observation found the milestone 115 job live at 917 of
1397 modules. Its incomplete progress is separate from this round's results.
Check the live process before any restart. The next selected task is the
actual-block assembly of the stronger endpoint count.

## Earlier record

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

See [the mathematical note](milestones/125-critical-six-count/MATHEMATICAL_NOTE.md),
[proof review](milestones/125-critical-six-count/audit/proof-review.md), and
[proof supplement](milestones/125-critical-six-count/audit/proof-supplement.md).
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

See [the mathematical note](milestones/124-six-count-cycle-pressure/MATHEMATICAL_NOTE.md),
[proof review](milestones/124-six-count-cycle-pressure/audit/proof-review.md), and
[coverage review](milestones/124-six-count-cycle-pressure/audit/coverage-review.md).
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

See [mathematical note](milestones/123-six-count-recovery/MATHEMATICAL_NOTE.md),
[proof review](milestones/123-six-count-recovery/audit/proof-review.md), and
[graph obstruction](milestones/123-six-count-recovery/audit/six-sum-guarded-review.md).
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

See [mathematical note](milestones/122-endpoint-equality/MATHEMATICAL_NOTE.md),
[proof review](milestones/122-endpoint-equality/audit/proof-review.md), and
[graph review](milestones/122-endpoint-equality/audit/endpoint-graph-review.md).
The next numerical target is the three all-four keys in
`milestones/122-endpoint-equality/data/next-six-four-cases.json`; inspect existing
seven-count coverage before searching. Paper revision 116 is unchanged; revise at 126.

## Earlier record

# Collaborator handoff

Checkpoint: 3 November 2026. Manuscript authors: Iori Hironaka, Tommy Ma, and Steven Zhan.

Latest continuation: [milestone 121](milestones/121-replacement-window-pressure/README.md) proves a sharp second-fourth count sum of 8 for 012032. Three complete attaining snakes and five new reference exclusions pass Lean; 1,358 entries remain. The 14,646 additional graph removals leave both numerical comparisons unchanged. Three native endpoint tests motivate the next conditional argument.

Start with [the current research handover](handoff/README.md). It records the completed case7305 theorem, five remaining local share targets, graph-interpretation gaps and the current comparison. The dated handovers and earlier entries below retain their historical evidence.

## Active empty-square route

Active research: [milestone 73](milestones/73-countfree-share-catalogue/README.md) now supplies four of the nine target count-free shares: 012031, 012304 and 012314 have floor 16; 012310 has floor 12. Coverage, canonical coordinate transfer, reversal, global share accounting and overlap are checked. The combined catalogue retains five local certificate premises. The full target 234 remains conditional on these, graph interpretation and potential replay. The maintained interval remains **191 <= a(9) <= 235**. Milestone 72 separately retains six unresolved count-certificate cases.

Count-free share continuation: [current comparison](milestones/80-012310-share-closure/README.md) verifies all 4,947,008 edge inequalities and an attaining cycle using checked local shares: mean 483, potential range 551 and integer comparison 235. Its weights and potential match the former comparison that assumed the 012310 lemma. The full target catalogue still has mean 496, range 600 and conditional bound 137941/587 < 235. The exact graph-to-snake and Lean potential assembly remains unfinished.

Preceding completed mathematical checkpoint: [milestone 71](milestones/71-proved-rule-conditional-pressure/README.md), on the conditional optimisation track. The forty recovered proved rules reduce the additional count premises for **234** from **18,788 to 14,155**, a reduction of **4,633 (24.66%)**. Independent verification checks all **3,533,981 retained transitions** and every mandatory-key witness. Recomputing the full conditional model raises its exact integer mean to **1492/3**, but the earlier potential needs fewer count proofs and is retained. Eight new Lean audits cover pruning and conditional arithmetic. The contributor-checked global interval remains **191 <= a(9) <= 235**. Selected count premises, complete graph-to-snake assembly and Lean graph-potential replay remain pending.

Current manuscript revision: [milestone 116](milestones/116-paper-revision/README.md). The paper incorporates the arguments through milestone 115 and retains one named definition, for the problem itself. All 13 printed snakes pass 118,673 vertex-pair checks. Authors, hyperlink settings and appendices are preserved. Source checks pass; the built-in compiler failed before TeX processing, so no current PDF or visual layout is verified. The next full revision is 126.

Next research priority: Certify the endpoint-placement hypothesis for equality in the 012032 pair bound, then prove its occurrence limit of 14 and test an endpoint credit with the full correction on both profiles. Retain the distinction between exact counts and the symbol-6 interval. Preserve the active 104 and 115 batches. Next paper revision: 126.

## Historical checkpoints

The entries below describe the evidence available at their original checkpoints.

The preceding paper revision is [milestone 43](milestones/43-full-paper-rewrite/README.md). It presents the complete argument for 236 directly, moves the earlier 238 proof to an appendix, and integrates the latest common-budget result with explicit verification limits. All 90 previous statement blocks and all printed witnesses are retained, with two accounting statements added. The existing editor source and repository paper are synchronized; authors and PDF settings are unchanged. The exact editor source compiles successfully.

[Milestone 42](milestones/42-six-count-state-model/README.md) completes a six-count finite model with exact normalized minimum cycle mean 42/11. An eleven-edge cycle and an integer potential checked on all 4,561,226 retained edges establish the finite-model result. Three Lean audits prove the common seven-window excess budget and combined charge arithmetic. All eleven critical windows are solver-UNSAT in a stronger local model, with no replayed refutations yet. There is no new global bound: the paper remains at 191 <= a(9) <= 236. The complete graph-to-snake Lean bridge is also pending.

The preceding local theorem is [milestone 41](milestones/41-joint-intervening-sum/README.md). For directions (a,b,c,d,e,c,a,d), first and seventh internal singleton counts at most three imply that the third and sixth counts sum to at least 12. Ten Lean audits passed, including a generic counter identity, the 5,222,602-hint replay, exact geometric interpretation, and overlap accounting. If the corresponding truncated counts sum to at most 11, each occurrence forces one excess unit; multiplicity two gives 12 charge units per occurrence. No occurrence-frequency lower bound is known. All 131 bank paths were checked: 1,442 direction-pattern occurrences, none meeting the two low-count caps. The global interval remains 191 <= a(9) <= 236.

The preceding local result is [milestone 40](milestones/40-intervening-counts/README.md). For directions (a,b,c,d,e,c,a,d), if the first and seventh internal singleton counts are both at most three, then the third and sixth counts are each at least five. Eight Lean audits passed, including both refutations and arbitrary coordinate normalization. These restrictions eliminate the saved 119/29 diagnostic cycle at its identified occurrence. Twenty-three independent local forest checks establish local attainments and controls; no new global bound or minimum cycle mean is claimed. The strongest manuscript interval remains 191 <= a(9) <= 236.

At milestone 39, the manuscript interval was **191 <= a(9) <= 236**. [Milestone 39](milestones/39-audited-bound-236/README.md) incorporates the completed radius-four theorem from contributor commit `7cb52aad`, with all 732 window refutations and a successful saved Linux dependency audit. The paper now supplies its full potential, boundary, endpoint, and incidence argument. An independent local enumeration checks 1,026,432 candidate transitions, and four new Lean arithmetic checks passed. The complete contributor proof has not been independently rebuilt here; selected proof interfaces and audit receipts are pinned separately from the earlier local proof build.

The preceding research checkpoint is [milestone 38](milestones/38-four-position-obstruction/README.md): 17 Lean audits prove asymmetric distance-four singleton restrictions. For directions (a,b,c,d,e,c,a,d), the first and seventh internal counts X,Y satisfy X >= 2, X <= 2 implies Y >= 4, and Y <= 1 implies X >= 9. Consequently X+Y >= 5, 2X+Y >= 8, and X+6Y >= 15. A qualifying distant singleton forces three units of count excess above the truncated value six. Seventeen local forests have independent checks, including boundary pairs (2,4), (3,2), and (9,1); full-snake sharpness remains unresolved. The saved diagnostic cycles survive these restrictions, and the integrated interval at that checkpoint was 191 <= a(9) <= 238.

The manuscript revision is recorded in [milestone 37](milestones/37-logical-paper-rewrite/README.md), dated 24 October. The main text now follows the complete square-identity, finite-window, potential-sum, and endpoint argument for 238. All 175 exclusions are printed; five Lean arithmetic audits and an independent check of 1,026,432 candidate transitions passed. Detailed classifications and search records are retained in appendices. The existing editor source is synchronized, with authors and hyperlink settings preserved. Compilation was blocked at that checkpoint; the current manuscript compiled successfully during milestone 40.

The preceding mixed-count checkpoint is [milestone 36](milestones/36-critical-cycle-consistency/README.md): two seven-centre mixed-count exclusions have passed six Lean audits, including arbitrary coordinate labels. They eliminate the previously saved critical cycles. The diagnostic witness-table mean rises from 1739/360 to 29/6; a replacement lower-table cycle remains at 119/29. The integrated interval at that checkpoint was 191 <= a(9) <= 238. Milestone35 retains the proved three-square share bonus and its occurrence accounting.

A foundational local theorem checkpoint is [milestone 33](milestones/33-distance-three-singletons/README.md), dated 23 October. Nine Lean audits establish distance-three singleton-sum bounds 10 and 9 for direction patterns `(a,b,c,d,e,b,a)` and `(a,b,c,d,e,b,f)`, respectively, with all named coordinates distinct. A disjoint six-cycle argument explains both bounds. There are no conditions on the intervening counts. The 131-path bank supplies 956 checked occurrences. The pair inequalities raise the recorded witness-table cycle mean from 287/60 to 1739/360; the lower-table mean stays 119/29. These diagnostic means do not establish a global bound.

[Milestone 32](milestones/32-seven-count-four-screen/README.md) has 18 Lean audits covering arbitrary-snake normalization, the 34-case classification, a conditional frequency consequence, and four completed geometric refutations. The remaining 30 numerical cases still need replay or deduction from other theorems; six consecutive singleton counts equal to four remain conjecturally excluded. All 34 native certificates have been generated, with pending exports kept as local intermediates. [Milestone 31](milestones/31-joint-counter-soundness/README.md) retains its completed weighted joint-excess bounds. The integrated interval at that checkpoint was 191 <= a(9) <= 238.

Earlier pending result: the proposed sum24 over five intervening centres remains numerical; the generic counter lemma supports its interpretation, but a separate replay is required. The current research direction is stated above.

Latest GitHub refresh (26 October): `research/unconditional-241` is at `74ca83db`. The 635 new replay roots and the aggregate theorem for 235 are complete, with a saved standard-axiom audit at `b20346ee`. This replaces the previous unfinished status. The seven-centre framework aimed at 234 remains conditional; no completed 234 theorem was found in the reviewed update. The local review and exact snapshots are in milestone51/data/repository-check.json.

## Previous empty-square checkpoints

The user's latest instruction explicitly requests the s0 route, superseding the earlier construction-only division of work. [Milestone 28](milestones/28-direct-share-certificates/README.md) pins its tested support to `41797e3863e17be730f06e3a9c5df09bbc0d404d`, with its new share-clause soundness support. [Milestone 27](milestones/27-empty-square-packing/README.md) supplies weighted window packing, exact remainder loss, a checked disjoint-window recurrence, and precise conditional targets for 230/231.

All six new Lean audits passed. On saved eleven- and six-position periodic patterns, packing improves the share bounds from 1889/5 to 464 and from 717/5 to 245. These are conditional on the existing solver records; the local numerical premises have not been replayed here. Exact packing certificates, 240 exhaustive controls and all 131 bank-path checks passed. No new unconditional bound is claimed.

Milestone 28 proves that directions `(a,b,c,a,d,b)` with distinct coordinates cannot have five internal singleton counts `(2,4,5,3,3)`. The 1,795-clause core and its geometric bridge passed Lean with standard axioms only. Although discovered under a share cap, the proof uses only ordinary window clauses. Nine of eleven new missing windows are solver-excluded without shares; eight still need certificate replay. A surviving window with directions `012304` and counts `(4,5,3,3,5)` has a saved acyclic local configuration with share **104**, independently counted. It prevents a blanket local bound of 108, without claiming extension to a complete snake. An independent CP-SAT implementation supports the existing 301 bound; the 163/245/pair-10 runs are UNKNOWN. The share encoder itself has finite controls and three checked arithmetic lemmas, not a completed universal soundness proof.

Next: certify the remaining ordinary exclusions, refresh the allowed-sequence graph, and choose share bounds on surviving windows that are essential to low-charge sequences. Then incorporate packing into a proof covering every allowed sequence, including boundary loss. The current five-window cache alone admits a saved periodic mean 42/11 with zero shares; separate pair/single-vertex share premises were omitted from that diagnostic. Optimizing selected cycles alone is insufficient. The finite-state construction must represent the packing recurrence or establish an equivalent invariant.

Final refresh: `research/unconditional-241` reached `8ad204ff`, reporting a larger solver-side share loop with 835 ordinary exclusions and 484 share bounds. Its period-three all-counts-four obstruction motivates the next complementary test: require the neighboring low-share windows to agree on a common selected-vertex set. Separate local witnesses need not be jointly realizable. `claude/relaxed-keller-60ks7i` reached `f83d139d`, adding a conditional 231 pipeline. Neither development is treated as a newly checked theorem here; reviewed snapshots are in milestone28.

The unfinished milestone 26 construction files remain local and are preserved. Their 186-edge interior-change witness does not improve the lower bound. Main still integrates 238; the collaborator's 237 audit remains branch-specific.

## Latest construction checkpoint

The earlier construction objective was any valuable improvement, without exclusive focus on 196. The current direction is recorded above.

[Milestone 22](milestones/22-internal-anchor-donors/README.md) tests the complete 191-edge donor through four anchor pairs and 23,040 alignments. No candidate of at least 192 edges survived; the five saved near candidates have 24 to 45 chords. Four new Lean audits certify the full donor and its relation to the prior prefix.

[Milestone 23](milestones/23-parity-compatible-faces/README.md) targets 193 to permit fixed-endpoint improvements. All 672 Q6 faces and 1,008 opposite Q5 pairs were solver-infeasible. One Q7 face remains unresolved after retries. At both 192 and 193, ten Q8 faces remain UNKNOWN and eight are excluded. Four Lean deductions check the target logic and third-neighbor exclusion.

[Milestone 24](milestones/24-contracted-face-search/README.md) implements that contraction and maximizes expanded length. Both the base and cycle-strengthened models passed 592 exhaustive controls. All twenty Q9 runs returned FEASIBLE at 191; none proved optimality. Five Lean results establish path contiguity, the count identity and the position obstruction to cycles. The complete optimizer correspondence remains a written argument with finite controls.

[Milestone 25](milestones/25-alternative-fillings/README.md) explicitly maximizes changed selected vertices at lengths 191 and 190. Four faces gave seven feasible paths and one UNKNOWN. The changed 191-edge path is equivalent to bank example 130. The most changed 190-edge path is exactly a new endpoint followed by a 190-vertex tail of that known path. Six growth attempts reached at most 191; all four recovered 191-edge paths matched bank example 130. Eight searches requiring the new vertex to remain selected returned UNKNOWN. The models passed 608 plus 256 exhaustive controls, and three Lean results passed with standard axiom audits.

Next: require an interior change as well as retaining the new vertex, then compare each candidate with the known bank before growth. The observed endpoint modification is not evidence of a new construction class.

GitHub refresh: `research/unconditional-241` reached 5fb6c286 with clause-collector settings, and `claude/relaxed-keller-60ks7i` reached e2d9f7fc with a seven-centre certificate generator. The earlier successful 237 audit at 2a7fe4e4 remains recorded separately. Main's integrated theorem remains 238; the 237 source closure has not been imported or independently rebuilt here.

## Construction history

This investigation now concentrates on a 196-edge construction; collaborators
continue the upper-bound work. The [new construction milestone](milestones/12-construction-196/README.md)
records a Lean-checked zero-defect criterion, approximately 31 million pilot
proposals, and exact fragment-repair experiments. No valid improvement over
191 edges was found. The two best 196-edge walks have seven chords each.
That initial experiment is now followed by the
[population and adaptive-repair comparison](milestones/13-diverse-construction/README.md).
The added 440 million proposals found no valid improvement; the best saved
walks have six chords. Retaining multiple candidates showed no consistent
benefit at the longer budget. Every saved best walk from those four long runs
has a known bank prefix and all defects touching its five appended vertices.
Four solver-guided interior repairs ended unresolved. The next constructive
direction relaxes connectivity, allowing a path and cyclic components, then
excludes those cycles using the existing checked cycle-exclusion lemma.
This is now implemented in [milestone 14](milestones/14-component-construction/README.md).
A concrete 197-vertex seed consists of one 14-edge path and seven 26-cycles;
its vertex count, degrees, partition, and cycle-cut validity passed Lean.
Sequential cycle cuts produced a 40-edge path and six 26-cycles on the same
number of vertices. The next round was unresolved. Continue from the saved
seven-component state with both accumulated cuts retained. It remains a
disconnected intermediate configuration, not an improved snake witness.

Further targeted mergers are recorded in [milestone 15](milestones/15-component-mergers/README.md).
The fixed 40-edge path is locally blocked, while unrestricted replacements of
the path and one or two cycles remained unresolved. The signed frozen-cycle
constraint has a Lean proof. [Milestone 16](milestones/16-cycle-reservoirs/README.md)
supplies two checked disjoint 14-cycles in Q5, a 224-vertex product, and additional
197-vertex disconnected states. The next constructive task is to use its two
4,973-row local-state tables in a global cell model. Four shared connector
vertices govern cross-cell edges; a checked local cost lemma explains why a
connector with four internal neighbors must omit at least three when it uses
an external edge. Costs can overlap and do not give a global bound.

Synchronization incorporated the completed KEEP=112 aggregate receipt covering
all 262 oriented bank entries, the bounded KEEP=96 survey, and conditional
window bounds through 238. The separate `research/unconditional-241-only`
branch at `890c486` contains an unconditional 241 theorem and a saved successful
audit. That branch was inspected, not independently rebuilt or merged here.
Historical priorities below describe previous checkpoints; they do not assign
new upper-bound work to this constructive investigation.

## Where the investigation stands

The exact optimum is unresolved; no candidate value receives privileged status. The earlier conjecture **a(9) = 196** has low confidence. For n = 3,...,8, subtracting 3*2^(n-3) from the known maxima leaves 1,1,1,2,2,2. Continuing the correction in doubling blocks of three predicts 196. An equally exact additive-block fit predicts 195. The first eight values therefore do not determine the ninth, and interpolation supplies no geometric proof.

The fully Lean-checked global interval is now **191 <= a(9) <= 241** (see the window-exclusion section below). The 245 argument: the strengthened square-face bound combines the incidence identity with endpoint singleton counts at least four, count-one neighbors at least four, and exclusion of three consecutive internal count-two vertices. The earlier arguments still supply the weaker bounds 247, 248, 251, 254, and 255. No 192-edge improvement, 196-edge construction, exclusion of 197 edges, or exact optimality result has been obtained.

The strongest completed global upper bound is 245. Normalization from arbitrary path indices, both five-vertex window shapes, all outer missing-family cases, the final shared-coordinate classification, and the aggregate potential estimate are checked in Lean. An independent final import audit passed. All theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The fresh source-only reproduction succeeded for all151 steps, including the148 strengthening modules, with every source hash rechecked. Saved manifests and logs are in `outputs/strengthened-reproduction-*` and the versioned `outputs/strengthened-245-reproduction-*` files. The exact optimum remains open.

The earlier universal two-singleton-square claim for internal vertices is false. A checked 137-edge counterexample has zero at path index 127, endpoints 145 and 288, and exactly one singleton square, {0,4,8,12}. Its distance along the path from the nearer endpoint is ten. Thus simply excluding the first few vertices near the endpoints does not repair that universal assertion. This example does not exclude a stronger statement restricted to longest paths.

## Window-certificate checkpoint, 16 October 2026

The repeated-coordinate radius-three (2,2,3) Boolean certificate passed all 61 Lean modules and its final axiom audit. The distinct-coordinate certificate is still being checked. The completed counter proof connects actual singleton counts to the ordered lists of 21 eligible corners and supplies the full auxiliary threshold assignment. Endpoint rules and all 112 retained cycle cuts are also checked. Exact assembly of all Boolean input clauses and arbitrary-window coordinate normalization remain open, so the global interval is unchanged.

See [milestone 07](milestones/07-window-223/README.md) for the source hashes, reproduction commands, and remaining obligations. The collaborator branch review is recorded [separately](milestones/08-exhaustive-search/upstream-review-2026-10-16.md); its restricted DFS results do not settle the global optimum.

## Completed milestone: incidence proof

The formerly pending upper-bound verification is complete. `work/spectral/SquareIncidence.lean` proves the following quantities directly from the cube and path definitions:

- E: total number of empty squares counted from each possible corner.
- T: total singleton incidences, counted at their selected vertex.
- W: total selected centers with both neighbors in a distinct coordinate pair selected.

For a path on v vertices, the checked identity is

`2*E + 4*T + 144*v = 36864 + 4*W`.

The checked estimates T >= v and W <= v-2 (for v >= 2) give v <= 255, hence at most 254 edges. The proof handles all path lengths. It uses the same snake definition as the 191-edge witness and assumes no census equation.

This replaces the need to certify all original canonical-square bijections before establishing 254. The old conditional arithmetic module remains as a record of the first approach. The exact canonical census equalities have not separately been certified; they are unnecessary for the new theorem. The paper now presents the checked proof.

Reproduce with `python work/spectral/verify_incidence.py --mathlib-dir /path/to/mathlib --fresh-core` after preparing the pinned dependency.

## Completed milestone: adjacent singleton exclusion and bound 251

Write alpha(x) for the number of singleton coordinate squares at a selected vertex x. The new theorem states that two adjacent internal path vertices cannot both have alpha = 1. At a normalized internal vertex with selected unit neighbors a,b, a unique missing pair c,d forces every other eligible pair vertex to be selected. The continuation through a must use c or d; otherwise three distinct selected vertices would have degree at most one. Applying this geometry at the adjacent vertex yields either three disjoint groups each requiring an endpoint, or a selected eight-cycle. Both are impossible in an induced path.

Together with alpha >= 1, this gives alpha(x)+alpha(y) >= 3 for consecutive internal vertices. The checked finite-sum argument handles both endpoints and all short paths, and gives 3*m <= 2*T for a path with m edges. Substitution in the same incidence identity proves m <= 251. No solver exclusion is used in this proof.

The maintained proof sources are `work/spectral/stronger/`. Reproduce the full strengthened proof with `python work/spectral/verify_strengthened.py --mathlib-dir /path/to/mathlib`. This driver always builds a fresh source-only core, then the incidence theorem and all strengthening modules, and audits the final interval and general prefix theorem. Per-step logs and a SHA256 manifest are retained in its ignored build directory. The research directories retain explicitly frozen development snapshots, not alternative maintained proof projects.

## Completed milestone: adjacent counts (1,2) and bound 248

The next local theorem excludes adjacent internal singleton counts (1,2). After translating the count-one vertex to zero, its unique missing pair forces the root geometry as above. At its count-two neighbor, exactly two missing coordinate pairs remain. The proof treats all possibilities for their incidence with the other root arm: neither missing pair contains it, a missing pair uses the root's exceptional coordinate, two pairs use the arm, or one does and the other does not. Every branch forces more than two distinct path endpoints or a selected cycle. The finite-set classification and geometric contradictions are checked in Lean without solver premises.

Consequently every consecutive internal pair has singleton-count sum at least four. Including both endpoints gives `4*m <= 2*T+2`; the same incidence identity then proves `m <= 248`. `UpperBound248.lean` combines this unconditional upper bound with the existing 191-edge witness. The reproduction command above now checks both strengthenings and the final 191--248 interval.

## Completed milestone: endpoint count four and bound 247

At an endpoint, translate its sole selected neighbor to unit coordinate a. Singleton squares correspond to missing pairs among the other eight coordinates. Three or fewer missing pairs leave either at least three isolated coordinates, or exactly two isolated coordinates and three disjoint missing edges. The first case creates three endpoint demands. The second forces selected triples that prevent the neighbor a from continuing, again creating too many endpoints. The normalization, finite-family classification, and geometric contradictions are all checked in Lean.

Combining endpoint counts at least four with the internal pair sum at least four gives `4*m+10 <= 2*T`. The incidence identity proves `m <= 247`. A separate checked 120-edge path attains exactly four singleton squares at its first endpoint, so that local estimate is sharp. The reproduction driver checks the unconditional `verified_interval_191_247` and all preceding strengthening theorems.

## Completed local strengthening: adjacent counts (1,3)

`AdjacentOneThreeExclusion.lean` unconditionally excludes adjacent internal counts (1,3), so an internal neighbor of an internal count-one vertex has count at least four. A symbolic finite-set argument with three missing pairs produces either three disjoint endpoint groups, or two such groups and an additional group from isolated coordinates. Every step and arbitrary-index normalization is compiled with the standard foundations only. This milestone had41 maintained modules. The local theorem alone did not improve247, because an all-two internal count sequence still satisfied those adjacent restrictions.

## Completed milestone: no three consecutive twos and bound 245

`UpperBound245.lean` proves that three consecutive internal vertices cannot all have singleton count two, and derives the unconditional interval191--245. The proof first normalizes the five-vertex window into repeated- or distinct-coordinate shapes. The latter's outer missing families reduce through exceptional, common-hole, star, mixed, equal-pair, and disjoint-pair cases to ordinary pairs sharing one coordinate. A kernel-checked finite classification reduces this last case to20 labelled middle families, all excluded by explicit endpoint, degree, or cycle arguments. Every coordinate reduction is proved; no solver result or incomplete bank census is assumed.

For v selected vertices and total singleton count T, a finite potential yields `3*T >= 7*v+5`. The incidence identity and `W <= v-2` give `T+35*v <= 9214`, hence `112*v <= 27637`. Therefore v<=246 and the edge count is at most245. The final theorem uses the original `Snake9.Snake` and the original checked191-edge witness. The project now has148 maintained strengthening modules.

The next priorities concern improving beyond245 and finding a longer verified construction. Probes excluding adjacent counts (1,4) and two internal count-one vertices at path distance two remain uncertified observations. A checked (2,2) example prevents assuming every adjacent pair has sum at least five. The repeating count pattern (2,2,3) still meets the established local count restrictions and is a bottleneck for improving their aggregate consequence.

## Latest aggregate work: window exclusions (17 October 2026)

`milestones/10-window-aggregate/` addresses "Priority 2" below. Because `alpha >= 2` fails universally, it bounds how often low counts can occur, via local window exclusions rather than a pointwise bound.

- The radius-three local model allows only 144 of the 216 count triples in 1..6. The resulting aggregate ceiling is mean 14/5, versus 7/3 from the proved premises.
- With (2,2,3), (2,2,4), (2,3,2), (3,2,3), and (4,1,4..6) excluded, the Lean theorem `upper_242_of_certified_windows` gives 242 edges. A fresh 156-step source-only reproduction, in `outputs/strengthened-window-reproduction-*`, also re-proved 245.
- Also excluding (2,4,2,3), the theorem `upper_241_of_certified_windows` gives 241 edges.
- **These 22 exclusions are now Lean theorems, so 242 and 241 are unconditional** (`UpperBound241.lean`: `upper_bound_242`, `upper_bound_241`, `verified_interval_191_241`, axioms `propext`, `Classical.choice`, `Quot.sound` only). `LocalWindowBridge.lean` moves each snake window to canonical position and proves the abstract axioms of `LocalWindowModel.lean` there; `LocalWindowSat/` proves that every clause of each UNSAT core follows from those axioms; and `LocalWindowUnsat/` replays the drat-trim LRAT refutation of each core, segment by segment with `decide +kernel`, through the checker `LratCheck.lean`, whose soundness is proved in Lean. Audited on macOS (`outputs/upper-bound-241-audit.log`) and from a fresh Linux environment (`outputs/upper-bound-241-audit-linux.log`).
- All 22 premise cases have `drat-trim`-verified refutations of explicit CNFs, and 532 real-snake windows pass as positive controls.

- A direction-aware automaton (last six transition directions up to relabelling, last three counts; 2592 states) refined against the SAT oracle reaches mean 10/3 with 145 certified windows. `upper_239_of_direction_windows` gives **239 edges**; the potential table is kernel-checked and the parity bridge from `Snake9.Snake` is proved. With five-centre windows the same loop reaches 7/2 with 325 certified windows and `upper_238_of_direction_windows5` gives **238 edges** (44,064 states, kernel-checked in 34 shards).

Remaining work to make 239 or 238 unconditional: the same pipeline applies. For 239 the direction-aware bridge (`LocalWindowDirBridge.lean`, `DirectionWindowBridge.lean`) and the clause soundness of all 145 cores (`LocalWindowSat/D*`) are proved; what remains is the kernel replay of the 145 LRAT refutations (2575 kernel-check modules, generated by `milestones/10-window-aggregate/scripts/run_direction_replays.py`) and the final compile of `UpperBound239.lean`. For 238, the 325 five-centre windows need the bridge, cores and replays.

Untested four-vertex windows were counted as feasible, radius four was not used, and the empty-square term `s0` is still discarded. 241 is therefore not the limit of this method.

## Priority 1: find a longer construction outside the exhausted families

A verified 192-edge example would immediately disprove the candidate optimum 191. A 196-edge example would establish the conjectured lower bound, but still would not prove optimality.

The current evidence favors widening structural diversity over repeating small changes to the same seeds:

- Every 152-vertex prefix obtained from either orientation of the 131 supplied 191-edge snakes was exhausted without reaching 193 vertices. With only 144 vertices retained, 53 searches remained unresolved at the node limit.
- Every two-vertex-deletion neighborhood of the 131 examples was excluded for a 192-edge target by the solver. Larger neighborhoods remain largely unresolved.
- The supplied 98-edge Q8 seed has no 97-edge partner under the tested exact one-crossing joining model, at either endpoint. Isometric placements of the tested truncated copy also fail. This does not classify all optimal Q8 seeds.

Useful constructive directions are structurally different Q8 seeds, constructions with multiple crossings between layers, and larger changes that replace internal portions and endpoints together. The exact joining theorem states that projected layer paths must intersect only at their joining endpoint. Compatible lengths 98 and 97 would produce 196; compatible lengths 98 and 98 would produce 197 and refute the present conjecture. Testing 197 should remain part of the investigation.

A C bitset search (`milestones/08-exhaustive-search/dfs_investigation.md`) has since exhausted end regrowth with up to 80 freed vertices at either end of every bank snake, without reaching 192 edges. It also shows that internal windows of the bank snakes are nearly frozen, and that the known 98-edge Q8 seed has no alternative optimal completion when 59 vertices are freed. Parity forbids reaching 192 by internal replacement alone. The most promising remaining routes are (a) a full classification of 97/98-edge Q8 snakes, which would decide the single-crossing (98,97) and (98,98) cases exactly, and (b) generating new 191-edge basins from scratch rather than perturbing the bank.

**Lean-checked progress on this route.** `DfsParity.lean` proves that internal rewiring of a 191-edge snake can never give 192 edges. `DfsDecide.lean` is a kernel-friendly exhaustive search with verified parity and leaf-peeling bounds, and `bank_no192_keep160` proves that no 192-edge snake shares a 160-vertex end segment with any bank snake. With version 2, `bank_no192_keep152v2` extends this to 152-vertex end segments: 2616 kernel-checked theorems in 60 modules covering about 2.2e5 search nodes, in 40 minutes on three cores, with the same axiom audit. Deeper certificates cost about 6x more per 8 freed vertices; see `milestones/08-exhaustive-search/dfs_investigation.md`.

An alternative is an induced cycle on 194 vertices, which yields a 192-edge snake after deleting one vertex. Four restricted symmetric cycle searches returned UNKNOWN; asymmetric constructions remain available. None of these routes is guaranteed to succeed.

The joint-search route now has a checked starting point: bank example 0 decomposes into compatible 96- and 94-edge Q8 paths, and its 191-edge join is Lean-checked. A new model varies both paths. It passed 42 exhaustive small-cube controls and the fixed 191-edge benchmark. Searches for (98,97), (98,98), and (96,95) each returned UNKNOWN at 120 seconds; the last used the checked pair as an unfixed hint. See `milestones/02-layer-constructions/joint_layer_investigation.md`. These results establish no exclusion of any target. Consider diverse hints or multiple-crossing models rather than treating the timeouts as structural evidence.

## Priority 2: obtain a much stronger global restriction

The square-count identity could support stronger bounds through aggregate constraints on empty and singleton squares. The universal local bound alpha >= 2 is already false, so any stronger statement needs a justified restriction or an aggregate correction.

All 131 published 191-edge examples have minimum local alpha at least three: 67 examples have minimum three, 47 have minimum four, and 17 have minimum five. This is a dataset observation, not a theorem about all long or optimal snakes. A useful investigation is whether a low-alpha configuration forces enough structural loss elsewhere to exclude sufficiently long paths. Search for counterexamples to any proposed inequality before using it in a proof.

For exact optimality, proof-producing exhaustive computation or a structural classification would be needed if analytic bounds remain weak. The current global solver returned UNKNOWN at 192 edges, and supplies no impossibility certificate. Scaling it without a symmetry argument or certifiable decomposition is an uncertain long-term route.

## Suggested division of work

- Proof contributor: independently review the completed incidence proof, then prove stronger aggregate inequalities or long-path restrictions.
- Construction contributor: diverse Q8 seeds, multiple layer crossings, and asymmetric cycle constructions.
- Extremal contributor: long-path restrictions on low-alpha configurations and aggregate square inequalities.

These are independent tasks suitable for separate branches. The current handoff assigns no person and sends no messages to collaborators.

## Evidence map and working conventions

| Material | Location |
|---|---|
| Current mathematical paper | `paper/snake9_research.tex` |
| All standard-library proofs | `work/final_lean/` |
| Bounds 241, 242, 245, 247, 248, 251, 254 and 255 using pinned mathlib | `work/spectral/` |
| Audits of the unconditional 241 and 242 bounds | `outputs/upper-bound-241-audit.log` (macOS), `outputs/upper-bound-241-audit-linux.log` (fresh Linux build) |
| Fresh 245 build and verified source hashes | `outputs/strengthened-reproduction-manifest.json`, `outputs/strengthened-reproduction.log` |
| Fresh core and incidence build | `outputs/incidence-reproduction.log` |
| Square investigation and its limitations | `milestones/03-square-incidence/square_investigation.md` |
| Layer construction and restricted exclusions | `milestones/02-layer-constructions/layer_investigation.md` |
| Competing trend fits | `milestones/01-foundations/trend_hypothesis.md` |
| Explicit witnesses and search records | `outputs/*.json` |
| Published 131-example subset | `work/bank9.json` |

The authoritative standard-library Lean sources are in `work/final_lean/`; maintained mathlib-dependent proofs are in `work/spectral/` and `work/spectral/stronger/`. Do not create divergent proof copies in `outputs/`. The authoritative paper is the existing LaTeX source. Keep implementation filenames and theorem identifiers in technical notes rather than the paper. Retain Iori Hironaka, Tommy Ma, and Steven Zhan in the author field. Contributor PDFs are snapshots; the maintained main paper is the TeX source.

A search timeout, a blocked endpoint, and a restricted exclusion cannot establish global optimality. For every claimed theorem, state exactly which assumptions are discharged. The repository is a research checkpoint, and its documentation must retain the unresolved status until a matching construction and global upper bound are verified.

## Additional local research direction: certify the radius-five obstruction

The latest experiments sharpen the remaining split-arm case. A radius-four forest is feasible with at most two interior endpoints. At radius five, the solver reports infeasibility with budgets two and three, while finding a forest with budget four. Allowing cycles restores feasibility at budget two. The saved feasible assignments passed independent Python checks; the exclusions remain uncertified. See `milestones/04-singleton-geometry/low_singleton_investigation.md` and the seven accompanying JSON records.

A checked Boolean certificate for radius five and budget two is now available. Its geometric interpretation remains a separate proof obligation; the current numerical priority is the (2,2,3) restriction described below. The general-to-normalized geometric reduction is also unfinished. The certificate for the encoded model leaves this reduction to prove. These experiments do not change the global interval.


The upstream split-arm proof, radius-three forest certificate, and ball-search records remain included; see `milestones/04-singleton-geometry/low_singleton_investigation.md`. Their restricted solver exclusions are not premises of the 245 bound.

## Integrated Boolean certificate investigation

The separately developed radius-five experiment now has a Lean-checked contradiction for an explicit core of 567 clauses and 252 Boolean variables, using 398 derived clauses. All 41 recorded cycle cuts and the general degree/endpoint clause rules are also checked. The complete interpretation of the concrete input clauses as geometric conditions on a snake is unfinished. See [the certificate investigation](milestones/06-radius-five/ball_certificate_investigation.md) for the evidence boundary and reproduction instructions.

This work does not improve the unconditional bounds. Its earlier conditional 250 arithmetic is retained as historical motivation, rather than a current strengthening target. The exclusion of the singleton-count pattern (2,2,3), the premise of the conditional bound 244, is now one of the 22 Lean-proved window exclusions behind the unconditional bound 241. The Boolean-certificate method may provide an independent route to local geometric exclusions.

## 16 October 2026 integration and organization

GitHub PR2 is integrated at b0a78f1. The main paper is now `paper/snake9_research.tex`, with both authors and the local hyperlink settings preserved. All maintained TeX files live under `paper/`; milestone folders separate investigations. Historical raw data and shared proof projects retain stable paths.

The fresh pre-DFS rebuild succeeded: 153 steps, 172 source hashes, 343 theorem axiom audits. See `milestones/05-upper-bound-245/integrated-reproduction-manifest.json`. This does not claim a new independent rebuild of every incoming DFS certificate.

The (2,2,3) work is in `milestones/07-window-223/`. Both radius-three encodings have solver proofs and independent Python replay; both large Lean translations exhausted memory. Splitting their proof declarations into separately compiled modules is the next implementation step. The geometric interpretation and arbitrary-window reduction remain required before 244 can be asserted from these encodings; (2,2,3) has since been excluded in Lean by the route of `milestones/10-window-aggregate/` (bridge, core soundness, LRAT replay), so 244 and 241 hold unconditionally.
