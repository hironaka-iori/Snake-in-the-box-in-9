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

See [the mathematical note](../milestones/125-critical-six-count/MATHEMATICAL_NOTE.md),
[proof review](../milestones/125-critical-six-count/audit/proof-review.md), and
[proof supplement](../milestones/125-critical-six-count/audit/proof-supplement.md).
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

See [the mathematical note](../milestones/124-six-count-cycle-pressure/MATHEMATICAL_NOTE.md),
[proof review](../milestones/124-six-count-cycle-pressure/audit/proof-review.md), and
[coverage review](../milestones/124-six-count-cycle-pressure/audit/coverage-review.md).
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

See [mathematical note](../milestones/123-six-count-recovery/MATHEMATICAL_NOTE.md),
[proof review](../milestones/123-six-count-recovery/audit/proof-review.md), and
[graph obstruction](../milestones/123-six-count-recovery/audit/six-sum-guarded-review.md).
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

See [mathematical note](../milestones/122-endpoint-equality/MATHEMATICAL_NOTE.md),
[proof review](../milestones/122-endpoint-equality/audit/proof-review.md), and
[graph review](../milestones/122-endpoint-equality/audit/endpoint-graph-review.md).
The next numerical target is the three all-four keys in
`milestones/122-endpoint-equality/data/next-six-four-cases.json`; inspect existing
seven-count coverage before searching. Paper revision 116 is unchanged; revise at 126.

## Earlier record

# Research handover

Read [current status](CURRENT_STATUS.md), [next steps](NEXT_AGENT_PROMPT.md),
and [milestone 121](../milestones/121-replacement-window-pressure/README.md).

For every 012032 window, the second and fourth internal singleton-square counts
are each at least 2 and sum to at least 8. Lean checks the three local refutations,
actual-snake interpretation, reversal and resulting inequalities. Complete
snakes of 142, 138 and 144 edges attain the respective pairs (2,6), (3,5) and (4,4);
their paths, directions and pair counts also pass Lean. The pair bound is sharp
for actual snakes. No new mathematical definition is introduced.

Five further reference cases are discharged. Twenty entries are now checked,
and the exact remaining obligation has 1358 entries. The final proof checks cover
40 modules and 47 printed axiom reports, including the three boundary witnesses
and a separate conditional charge inequality. Standard foundations only occur
in the reported dependencies.

The pair restriction removes 14,646 additional graph transitions, including two
edges of the former conditional cycle. A replacement four-cycle keeps mean 496,
range 602 and integer comparison 234. The other profile retains its eighteen-cycle,
mean 2915/6, range 1730/3 and comparison 235. Both graph experiments retain inherited
unproved sum hypotheses and global assembly work. The local theorem and sharp
witnesses establish no improved global upper bound.

All three sharp witnesses place both endpoints at distance two from both counted
vertices. Three full-Q9 tests demanding an endpoint outside that intersection
return native UNSAT without cycle cuts. Their encodings have been audited, but
the refutations and actual-snake endpoint interpretation remain unchecked.
The proposed endpoint-necessity theorem is therefore a hypothesis.

If proved, it would limit equality to fourteen windows in any snake and rule
out equality in odd-length snakes. Those deductions have written arguments and
a finite sphere-intersection check; their general Lean proofs remain pending.
Lean already checks the conditional arithmetic with the 14C correction. This
does not supply its missing geometric or occurrence-count hypotheses.

The maintained interval remains 191 through 235 edges, with the contributor proof
and archived audit for 235 and its complete independent rebuild pending.
Conditional 234, the optimum and 196 remain unresolved. Paper revision 116 is
unchanged; the next full manuscript revision is 126. The two pre-existing proof
batches remain active; their exact process observations are in the checkpoint.

Certify the three saved endpoint contradictions for boundary pairs (2,6), (3,5)
and (4,4). Each formula is the ordinary full-Q9 window encoding plus one clause
requiring an endpoint outside the intersection of the two exact distance-two
spheres. Rebuild and replay the saved negative cases before proving that extra
clause sound under an actual counterexample. The existing actual pair theorem
and reversal then reduce the equality case to these three inputs.

Prove the resulting occurrence limit 14 and its odd-length consequence. Evaluate
an endpoint credit on both graph profiles with the full 14C budget correction.
Initially award it only to exact pairs (3,5), (4,4), (5,3): clipped symbols (2,6)
or (6,2) may have actual sum greater than 8. The surviving completed-profile cycle
has no 012032 window, so this credit alone cannot improve its cycle mean. Keep
that limitation explicit when deciding the next numerical experiment.

Do not rerun the same bounded probes merely to obtain another negative status.
Their exact inputs and encoding audit are saved in `data/next-endpoint-task.json`.
Preserve the active 104 and 115 batches and the pending 117/119 certificates.
