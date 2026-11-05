# Current continuation after round170

Round170: actual-cube component classification checked in Lean

The goal remains active. Five new Lean modules pass with19 printed theorem axiom reports. The actual candidate-family closure, pair support/parity, coordinate partition and clique implications, actual missing-edge reachability cuts, arbitrary-center translation, and four-corner empty-square equivalence are now checked. No new axioms or proof placeholders occur in accepted sources. The written e(q)>=8 and L<=95 domination consequence remain pending as complete Lean statements: numerical edge counts, unordered-pair/square cardinal correspondence, exact disconnected-case length, and global loss assembly still need checking. No numerical upper-bound improvement is claimed.

Every module has its own immutable execution plan, so changing a draft no longer invalidates unrelated accepted checks. Imported accepted source, object, log, receipt, toolchain, and dependencies are pinned and verified. The table-based pair-support draft exceeded the256MiB limit; algebraic bit support and parity replaced it and passed. Historical failures remain in logs. Small-module resource limits remain1GiB startup,768MiB reserve,256MiB compiler-private and60seconds. No compiler remains running at completion.

Next: finish graph counting. The existing local Mathlib theorem SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one is in Mathlib/Combinatorics/SimpleGraph/Acyclic.lean lines215 onward and gives Nat.card V <= Nat.card edgeSet +1. Use its existing proof when the larger2GiB startup profile is available. First interpret MissingReach as SimpleGraph reachability, then establish the unordered coordinate-pair/empty-square count bijection; avoid counting ordered pairs twice. The disconnected two-clique count and exact lengths14,26,34,38 need separate finite cardinal arguments. Full-paper revision remains next176.

---

Earlier records follow; weaker verification states and pauses are historical.

# Current continuation after round169

Round169: missing-pair components and a stronger undominated bound

The goal remains active. At an undominated Q9 center, the graph of absent coordinate pairs is either connected or exactly two clique components. Written proof and independent review give e(q)>=8 and L<=95 implies domination. If disconnected, the entire snake alternates between ab crosspairs and ab-1 triples; m=2ab-2 is14,26,34,38. All four cases have saved constructions checked for distinct vertices and every pairwise cube adjacency. Every undominated center of a longer snake has connected missing-pair graph.

Lean verification: seven modules have PASS receipts with 24 printed axiom reports, including the reused six-statement round167 module. New actual-cube pair/triple and endpoint deductions passed; the generic path-closure theorem passed. The finite eight-cycle endpoint inequality also passed. No new axioms, sorry, admit, or native_decide occur in accepted sources. Full component theorem is NOT yet Lean-checked: the actual candidate subset, its closure, outside witnesses, graph classification/counting, and final loss assembly remain.

Resource-safe change: rebuilt only required PathStructure lemmas and replaced finite cube identities with algebraic proofs. The current PathStructure peak sampled180121600 bytes and CubeLocal48136192 bytes. Existing limits unchanged. Historical failed attempts remain in logs and review; current accepted receipts are data/*-audit.json. Undominated167 reuses its original checked object and receipt; all source/object/log/dependency hashes were validated.

No new unconditional numerical upper bound. The conditional234 comparison still needs L>=4 for the relevant dominating snakes and all its other documented local/global premises. Next priority is actual-cube candidate-set closure and component theorem assembly, followed by restrictions on dominating small-loss cases. The six-square result from168 is superseded by the eight-square theorem in the manuscript. Full-paper revision schedule remains next176.

---

Earlier records follow; their pause and weaker-bound statements are historical.

# Active continuation: round 168

The goal has resumed. The two-round pause recorded below is historical.

New written result: an undominated Q9 snake vertex has at least six empty squares, so total loss at most 71 implies domination. Proof: the missing-pair graph with at most five edges either forces three endpoints directly or consists of P3 plus three isolated edges; pairs of isolated edges force disjoint closed eight-cycle subgraphs and too many endpoints. Independent written review found no gap. Native checks cover all 443704 simple coordinate graphs with at most five edges and all 16 triple selections per eight-cycle. These are not a complete Lean proof.

The actual-cube Lean source is drafted. The initial core Snake9 check passed, but its plan was superseded and that receipt is retained as historical. PathStructure exceeded the 256 MiB small-module limit; its finite adjacency test was replaced by an algebraic proof. Subsequent startup checks found less than the required 1 GiB available, so revised modules remain unverified. Existing large-replay limits remain unchanged. No compiler remains running.

Next: run the pinned round168 modules under the existing resource limits; finish the graph-counting and eight-cycle interpretation in Lean. The numerical bound remains conditional at 234, with no new unconditional bound. Both main-paper copies contain the new written proof. The short explanation remains a round167 snapshot with added reasoning.

---

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

Historical records follow.

# Round 166: exact small-loss restrictions and zero-loss countermodels

Six finite arithmetic statements passed Lean with no axioms. They cover
all possible Q9 degrees and incident-square counts, conditional on the
geometric bound e(q) <= choose(9-d(q),2). The geometric bound is proved
in the paper by assigning each empty square its two absent-neighbour
directions; that geometric interpretation is not newly checked in Lean.

Loss at most three excludes positive empty-square counts at degrees zero
and seven, excludes count two at degree five, and permits at most three
positive degree-five residues. Count five at degree five has zero residue.

The independent exact audit checks the explicit 191-edge snake (loss 163)
and all 131 bank snakes (loss 152 through 913). It also gives zero-loss
countermodels: a disconnected degree-two set; a disconnected set with
exactly two endpoints and cycles; an acyclic set with 64 endpoints; and a
union of sixteen six-cycles. None is a snake or a counterexample at 235 edges.
Thus no universal positive-loss bound has been established.

The existing paper and its repository mirror were updated in place,
reviewed against all 6,605 prior lines, and compiled by the editor. The
preamble, local hyperlink settings, and three authors were preserved.
The update integrates the exact loss budget, degree decomposition,
conditional 234 comparison, finite tests, and current replay status.
The first compilation returned stale-project; the retry succeeded.
The six Lean checks used the core library with a separate small-memory
profile. The initial core startup gate stopped before compilation; the
later run passed. The large replay's original resource limits remain
unchanged. Its accepted prefix is still 33,111 deductions.

Read experiment/FINDINGS.md for constructions, data/completion.json for
scope and hashes, and review/full-paper-review.md for the source review.
Last full paper revision: 166. Next scheduled full revision: 176.

Historical records follow.

# Two-round stopping point: milestones 164 and 165

The requested two additional rounds are complete. Research is stopping for
the user's requested pause. No research worker is left running.

Round 164 found a minimum potential range of 5411/9 at mean 4462/9 on the
retained conditional graph. Under total rounding loss at least 4, the
comparison is 235 - 3/42262, hence at most 234 edges. The positive-loss
premise and inherited graph-to-snake obligations remain unproved. Read
milestones/164-loss-corrected-potential/MATHEMATICAL_NOTE.md.

Round 165 checked five numerical arithmetic statements in Lean. It also
revalidated all 216 accepted replay modules. The next module could not
start because free memory was below the unchanged 2 GiB startup gate.
No new replay deductions were added. The accepted prefix remains 448
continuation segments in 14 complete groups: 33,111 deductions and
2,734,960 references, including the earlier prefix. There remain 112,104
deductions and 11,975,921 references. The full contradiction and the
actual-snake share-18 theorem remain pending.

No new unconditional upper bound is claimed. Read
milestones/165-share18-continuation-and-pause/COMPLETION.md and its adjacent
data/completion.json. Resume only after user authorization.
Last full paper revision: 156; next scheduled full revision: 166.

# Current result: extended share-18 proof checkpoint

Milestones 161 and 163 now connect 448 continuation segments in
14 complete groups to the original clause set through a Lean-checked
consequence theorem. Including the earlier prefix, this covers
33,111 deductions and 2,734,960 references.
There remain 112,104 deductions and 11,975,921 references.

Read milestones/163-share18-replay-continuation/COMPLETION.md and its adjacent
data/completion.json. Continue the existing161 replay in bounded batches,
reusing accepted modules. Its sources and execution plan are unchanged.
Historical publication manifests refer to their recorded commits; do not
expect their old progress-file hashes to match a later continuation.

The final geometry and reversal sources are compatible with the accepted
encoding and can be reused unchanged after the full contradiction passes.
The refutation wrapper must then consume that completed contradiction.
These final checks are still pending. The universal012034 share-18 theorem
and a new global upper bound are not established.

Seven additional arithmetic statements passed Lean. Retaining the existing
corner-share loss subtracts five times that loss from the comparison
numerator. At mean4462/9, range601 and correction0, an integer loss of at
least4 crosses the strict235 threshold. The packing and potential premises
remain explicit. Neither a positive global loss bound nor a compatible
full-graph potential was proved. Read
milestones/163-share18-replay-continuation/ROUNDING_LOSS.md and its adjacent
data/remainder-completion.json. This is a conditional refinement; the
unconditional numerical bound is unchanged.

Last full paper revision:156; next:166. Historical updates follow.

# Current result: extended share-18 proof checkpoint

Milestones 161 and 162 now connect 128 continuation segments in
4 complete groups to the original clause set through a Lean-checked
consequence theorem. Including the earlier prefix, this covers
13,535 deductions and 787,366 references.
There remain 131,680 deductions and 13,923,515 references.

Read milestones/162-share18-composition-plan/COMPLETION.md and its adjacent
data/completion.json. Continue the existing161 replay in bounded batches,
reusing accepted modules. Its sources and execution plan are unchanged.
Historical publication manifests refer to their recorded commits; do not
expect their old progress-file hashes to match a later continuation.

The final geometry and reversal sources are compatible with the accepted
encoding and can be reused unchanged after the full contradiction passes.
The refutation wrapper must then consume that completed contradiction.
These final checks are still pending. The universal012034 share-18 theorem
and a new global upper bound are not established.

Last full paper revision:156; next:166. Historical updates follow.

# Current result: first continuation group checked in Lean

Milestone 161 passed its twelve-module pilot: 32 continuation segments,
6,050 new deductions and 196,276 references. Together with
the accepted prefix, 7,105 deductions are now connected to the original
clause set through checked checkpoint consequences.

The remaining continuation has 138,110 deductions and
14,508,599 references. Its sources are already generated and pinned;
do not regenerate them or restart accepted modules. Read
milestones/161-share18-full-replay/PILOT_COMPLETION.md and its adjacent
data/pilot-completion.json before resuming scripts/run_replay.py in bounded
batches. The driver rechecks and reuses accepted objects.

The complete contradiction, actual-snake transfer and reversal are still
pending. The universal 012034 share-18 theorem and a new global upper bound
are not established. The completed interpretation in milestone 159 and
checkpoint in milestone 160 remain accepted.

Last full paper revision: 156; next: 166. Historical updates follow.

# Current result: checked share-18 replay checkpoint

Milestone 159 completed the interpretation of all 13,224 clauses in the
universal 012034 share-18 proof core: 109 modules and 108 axiom reports.
Milestone 160 reproduced the accepted 1,055-deduction prefix exactly and
checked three checkpoint modules in Lean. The new checkpoint inherits truth
from the original CNF; live clauses are retained and dead entries become
tautologies under the checked checkpoint rule.

Read milestones/159-share18-proof-continuation/data/semantics-completion.json
and milestones/160-share18-replay-transport/COMPLETION.md with its adjacent
data/completion.json. These stages are complete. Do not restart the old159
stopped batch or repeat its accepted clauses and structure checks.

Next continue the remaining 144,160 deductions and 14,704,875 references
from the checked checkpoint. Then check final contradiction assembly,
actual-snake transfer and reversal. The universal share-18 theorem and a
new global bound are not yet established. No new Boolean query is needed.

Last full paper revision: 156; next: 166. Historical updates follow.

# Current result: universal share-18 CNF interpretation completed

Milestone 159 passed the interpretation of all 13,224 clauses in the
012034 share-18 proof core: 109 modules accounted for and 108 axiom reports.
All original mathematical source bytes were preserved. The initial 106
checks and two final assembly checks are accepted. The historical missing-
dependency failure is resolved by a separately pinned environment.

Read milestones/159-share18-proof-continuation/MATHEMATICAL_NOTE.md and
data/semantics-completion.json. Do not restart the old stopped batch. The
complete contradiction replay, actual-snake transfer and reversal theorem
remain unfinished. No global snake bound has changed.

Milestone 160 prepares exact replay-prefix transport and a checkpoint.
Reuse the accepted initial tree and 1,055 deductions. The remaining full
replay has 144,160 deductions and 14,704,875 references. No new Boolean
query is needed. The selected count-conditioned case follows from the
universal theorem once that proof is complete.

Last compiled full paper revision: 156; next: 166. Historical updates follow.

# Current result: weaker local floor refuted

Milestone 158 completes the test prepared in 157. Lowering only the
conditional 012034 share floor from 18 to 17 cannot preserve the comparison
below 235, even after varying mean, potential range and nonnegative uniform
occurrence credit. A nine-cycle and nine-edge walk imply a comparison of
at least 235 + 175/42262. Six arithmetic statements passed Lean.

The disk-backed implementation reproduced the accepted 156 weights before
changing the floor. The final search and independent source-row audit are
complete. Read milestones/158-memory-bounded-floor-test/MATHEMATICAL_NOTE.md,
data/completion.json and NEXT_STEP.md. Do not restart the pending 157 test;
its question is resolved by this stronger result. Earlier stopped and failed
attempts are historical records, not current jobs.

This establishes a limitation of the specified conditional finite model.
It supplies no new unconditional snake bound and no proof that the true
optimum is 196. Remaining local, reference and graph-to-snake obligations
retain their scope. The next local investigation should alter the identified
cycle rather than retune the same three parameters.

The paper remains at its compiled full revision 156; both copies are
unchanged. The next full revision is 166, when the completed 158 result is
to be incorporated. Historical updates follow.

# Current checkpoint: weaker local share assumption

Milestone 156 established the exact retained-comparison optimum
551765/2348 = 235 - 15/2348. Its full paper revision compiled successfully.
This is a finite-method result, with no new unconditional snake bound.

Milestone 157 asks whether lowering the conditional 012034 share floor
from 18 to 17 still permits mean 496 and integer range 603 through 631.
Five Lean arithmetic statements exclude shifts and scalings of the old
potential and establish the necessary target range. The exact graph test
is prepared, with original weights reproduced before any change.

The launch stopped before graph loading: 2,430,287,872 bytes were available,
below the existing 3 GiB threshold. No graph worker or run directory was
created. Feasibility remains unresolved. Read
milestones/157-weaker-share-floor/CHECKPOINT.md for the exact resumption
command and data/checkpoint.json for the verified evidence record.

Do not restart completed work in milestones 155 or 156. All remaining
local, count, reference and graph-to-snake obligations retain their stated
scope. The optimum of Q9 remains open. Last full paper revision: 156;
next full revision: 166. Both paper copies remain identical.

Historical updates follow; their statuses describe earlier stages.

# Current result: exact limit of the retained comparison

Milestone156 is complete. The count-conditioned share17 theorem leaves the
minimum potential range at602. The exact retained-graph optimum, allowing
mean, range and nonnegative uniform occurrence credit to vary jointly, is
551765/2348 =235-15/2348. It is attained at mean496, credit0 and range602.
This is a limitation of the specified conditional finite comparison, with
no new arbitrary-snake upper bound.

All4,661,572 retained edge inequalities were checked in exact native
arithmetic. An independent selected-row audit verified the attaining
nine-edge walk and fourteen-edge cycle. Seven Lean arithmetic theorems
checked their implications; a complete Lean graph certificate remains
unfinished. The maintained191--235 interval and conditional234 obligations
retain their documented scope. The optimum of Q9 remains open.

Read milestones/156-potential-range-and-paper/MATHEMATICAL_NOTE.md and
data/completion.json. The full paper revision preserves the original
statements, proofs, mathematics, witness quotations, tables, authors and
preamble. Both existing sources are identical and compiled successfully.
No new definitions were introduced. Next full paper revision:166.

The next investigation checks whether weakening the conditional012034
share floor18 to17 can preserve the conditional234 comparison. First audit
saved deficit walks and cycles; do not repeat full graph optimization if
a surviving witness already rules out the required range below632.

Historical updates follow; their pending statuses describe earlier stages.

# Current result: local share 17 completed

The 137-module contradiction replay, 98-module interpretation and final
actual-snake composition are complete. The five local count conditions and
their reversed form remain hypotheses; universal012032 share17 is unproved.
The universal share16 theorem remains available without those restrictions.

Three short range implications have also passed Lean. In the specified
fixed profile with012301 and012340 floors16, the retained fourteen-cycle
keeps the comparison at least235-19/587. This limits this comparison's
ability to reach233; it is no new global upper bound.

Both existing paper sources were updated identically and the built-in
compiler succeeded. Authors and preamble are unchanged. The next full
paper revision is156, with a full review of current claims and historical material.
Read milestones/155-share17-replay/COMPLETION.md, its actual-snake completion
record, and analysis/RANGE_NOTE.md. The maintained interval and conditional
234 obligations retain their documented scope. The optimum remains open.

Historical updates follow.

# Research update: share-17 initial replay checked

The 34-module initial replay and checkpoint have passed Lean, covering
2,095 deductions and 6,002 propagation references with 106 axiom reports.
The full 137-module source export is prepared. Its runner reuses the 34
accepted modules and checks the remaining 103. The complete contradiction
and its final application to actual snakes remain pending.

Read milestones/155-share17-replay/PILOT_CHECKPOINT.md. Inspect its full
replay progress and actual process before starting or resuming a compiler.
After all 137 modules pass, audit the complete replay and check the separate
actual-snake composition. The share-17 count conditions remain required.
No new global bound is claimed. The paper already records the unresolved
contradiction. Last full paper revision: 146; next: 156.

Historical updates follow.

# Research update: broader critical-window interpretation checked

All 98 modules interpreting the shared share-17 certificate and transferring
it to actual snakes have passed Lean. The count conditions are alpha1=4,
alpha2<=4, alpha3=4, alpha4<=5 and alpha5=3, with reversed conditions for
reversed canonical directions. The contradiction remains an explicit
premise. The final share-17 theorem and any new global bound remain pending.

The universal 012032 share-16 theorem is complete in milestone 152. Next,
run the single share-17 replay in milestone 155, audit its pilot, then emit
and check the full contradiction and compose the actual-snake consequence.
Inspect live processes before starting another compiler. Use the v2 native
resource scripts. The original CIM monitor was delayed during a low-memory
event; its failed run and all accepted source bytes are preserved.

Broadening adds 100 source-graph rows and no retained rows. The retained
pair-sum condition forces the two relaxed counts back to 4 and 5. The
eleven-cycle still has two target edges. Last full paper revision: 146;
next: 156. Historical updates follow.

# Research update: universal 012032 share 16 completed

The complete contradiction replay and actual-snake composition have passed
Lean. Every fitting 012032 window, including reversal, has five-centre share
at least 16 without additional local-count assumptions. The recovered run
revalidated 301 accepted modules and completed all 342. The final theorem
and every saved dependency receipt were audited.

Read milestones/152-countfree-share16-completion/COMPLETION.md. Its completion
checkpoint is separate from the earlier running checkpoint. Four target
shapes remain for the conditional 234 route; other reference and potential
obligations remain. No new global upper bound is established.

Next: check the broader critical-context share-17 interpretation and its
single contradiction replay in milestones 154--155. Inspect their live
progress before starting another compiler. The old 147 job ended at reboot,
with 448 accepted modules preserved; it is not a currently held process.
Last full paper revision: 146; next: 156.

Historical updates follow.

# Research update: milestone 153

A complete numerical certificate supports the 012032 share-17 target under
counts alpha1=4, alpha2<=4, alpha3=4, alpha4<=5, alpha5=3, with reversal.
Removing two unused lower-bound counters preserves the compact core and
every compact proof step. Lean verification and the actual-snake theorem
remain pending. The exact evidence and remaining work are recorded in
milestones/153-pair-conditioned-share17/MATHEMATICAL_NOTE.md.

The computer restarted after the user pause. The old 151/152/147 processes
are absent. Recovery revalidates 301 accepted universal-share modules and
continues at the first unchecked one. Read the live recovery record at
milestones/152-countfree-share16-completion/data/reboot-recovery-v2-progress.json;
do not launch another replay or rely on the historical RUNNING records.
After it passes, audit the reboot recovery and use
`152-countfree-share16-completion/scripts/update_paper_after153.py`.
The 147 proof retains its accepted files; reschedule it after this check.

No new global bound is established. Last full paper revision: 146; next: 156.
Historical updates below describe their original checkpoints.

# Research update: milestone 152

The 012032 complete Lean replay is running; 154/342 modules are accepted
at the immutable checkpoint. Complete contradiction and final actual-snake
share16 remain pending. Their guarded audit and composition are already
queued. Read milestones/152-countfree-share16-completion/MATHEMATICAL_NOTE.md
and data/checkpoint.json before acting.

The same 012301 coordinator is temporarily held, not actively compiling.
The controller will resume it after the current batch; the queued final
check also preserves and resumes it. Revalidate live process identities.
Do not start another replay or restart completed proofs.

The bounded target17 query timed out; no stronger bound or sharpness result
was obtained. Exact inputs and incomplete output are archived. Paper copies
remain unchanged; a guarded update is prepared for proof completion.
Maintained interval191--235 retains the contributor rebuild caveat.
Conditional234 retains its other premises. Goal ACTIVE; full revision146,
next156. This running checkpoint will remain immutable after completion.

# Research update: milestone 151

The 012032 initial-state connection and first 32 replay segments passed
Lean: 3,728 deductions and 195,386 references, including the checkpoint
transfer. There are 49 accepted modules out of 342 prepared for the full
replay. Exact generated sources and accepted evidence are saved; the full
contradiction and actual-snake composition remain pending.

The same 147 job for 012301 resumed after both bounded batches. The next
selected task is the smaller remaining 012032 replay, using a guarded
controller to keep a single Lean compiler active and preserve that existing
job. Revalidate process identity and current progress before acting. The
completed 012310 proof and accepted 151 prefix must not be restarted.

Read milestones/151-countfree-replay-pilot/MATHEMATICAL_NOTE.md. Both paper
copies are updated, with no new definitions or preamble changes. The PDF
helper still fails before TeX. No new global bound; maintained 191--235
and the contributor rebuild caveat remain. Conditional 234 retains its
other premises. Goal ACTIVE; last full paper revision 146, next 156.

# Research update: milestone 150

The 012032 share-16 target now has a count-free numerical certificate:
58,182 deductions and 5,350,080 references. Its retained core uses none
of the added pair-count clauses or variables. All 112 Lean module checks
for the exact clause interpretation and conditional actual-snake transfer
passed. The complete contradiction remains an explicit premise.

The complete numerical transport and its independent audit passed. The
38-module initial-tree and prefix pilot is prepared and uncompiled. The
existing 012301 full replay remains the only active long Lean job; its
same coordinator resumed after this bounded batch. Inspect live progress
before acting. Do not duplicate it or restart the completed 012310 proof.

Read milestones/150-actual-pair-share/MATHEMATICAL_NOTE.md and its exact
checkpoint. Native inputs and packed transport are preserved in verified
archives. Both existing paper copies are updated without new definitions
or preamble changes. The compiler helper still fails before TeX, so no
new PDF is verified. The maintained interval is 191--235, subject to the
contributor independent-rebuild caveat. Conditional 234 retains its other
premises. Goal ACTIVE; last full paper revision 146, next 156.

# Research update: milestone 149

On the original 4,947,008-edge share graph, lowering the 012032 floor to 15
cannot be compensated by any uniform occurrence credit. The other eight
floors, event rule and occurrence allowance 24 are fixed. An eleven-cycle,
an unchanged three-cycle and a new 28-edge walk force the comparison to be
at least 235. Five arithmetic statements passed Lean; the exact saved
graph identities were checked separately. This is a limitation of that
specific graph argument, with no new global snake bound.

The 012032 share-16 target remains necessary in this profile. The selected
next step is still the existing 147 full replay, session 67526 and coordinator
PID 15228 at this checkpoint. The same process resumed after the short 149
arithmetic check. Revalidate it before any action; do not restart a live job.
The 148 conditional actual-snake transfer is complete. Its core contradiction
and prepared final composition remain pending.

See milestones/149-share-credit-tradeoff/MATHEMATICAL_NOTE.md and the saved
audit. Both paper copies were updated without new definitions or preamble
changes. PDF preparation still fails in the Windows helper before TeX.
The maintained interval remains 191--235 with the contributor independent
rebuild caveat. Conditional234 retains its other premises. Goal ACTIVE;
last full paper revision146, next156.

# Research update: milestone 148

The coordinate and reversal transfer for 012301 share 16 is checked. For every
fitting occurrence of either canonical orientation, the exact cap 15 core
contradiction implies a five-centre share sum of at least 16. No extra count,
parity or endpoint-location premise is needed. The core contradiction
remains an explicit premise; its full Lean replay is still running.

Sixteen module checks passed with 27 standard-axiom reports. One earlier
automaton data object is reused after source/object/log/dependency matching.
The remaining added helpers were checked from saved sources. Unnecessary
witness and old 239 table checks were removed from the transfer-only support
copies while their original sources and failed rebuilds were preserved.

The same 147 replay resumed after the bounded checks. Its session is 67526;
inspect the live process and progress before resuming anything. The final
composition source is prepared and guarded against premature compilation.
The completed 012310 count proof must not be restarted.

Maintained interval 191--235 and contributor rebuild caveat are unchanged.
Conditional 234 retains its other premises; 196 and the optimum are unresolved.
No new global bound. Goal ACTIVE. The paper states the conditional transfer
in both existing copies, with no new definitions. Source checks pass; the
built-in compiler failed before TeX, so no new PDF is verified.

Read [the checkpoint](../milestones/148-actual-snake-share-transfer/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next: 156.

## Earlier record

# Research update: milestone 147

The exact 012301 core interpretation is complete: 113 Lean modules,
12,977 core clauses and all six retained induced-eight-cycle exclusions.
The checked implication still assumes a contradiction of that core.
The 36-module replay pilot and the first 32-segment group pass. The larger
prefix covers 8,653 deductions and 195,344 propagation references, including
its checkpoint transfer. There are 47 accepted replay modules out of 1,789.

The complete 5,089-segment source and exact proof inputs are saved in
byte-verified archives. Full Lean replay, coordinate transport and reversal
remain required for the actual-snake share-16 theorem. Inspect live progress
before resuming; do not restart the completed 012310 count-sum proof.

The maintained interval is 191--235, with the contributor rebuild caveat.
Conditional 234 retains its premises; 196 and the optimum are unresolved.
No new global bound. Goal ACTIVE. The paper's verification paragraph is
updated in both existing copies, with no new definitions. Source checks
pass; the built-in compiler failed before TeX. No new PDF is verified.

Read [the checkpoint](../milestones/147-countfree-clause-semantics/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next full revision: 156.

## Earlier record

# Research update: milestone 146

The original-clause-to-initial-tree check is complete. Three Lean modules
with four accepted axiom reports connect all 104 chunks of the preserved
share-18 certificate to its initial tree and the checked prefix of 1,055
deductions and 6,006 propagation references. The full share proof remains
unfinished; no new global bound is claimed.

The full paper revision is saved in the open editor and repository. It
places proved results before current conditional comparisons and retains
earlier work in appendices. Mathematical statements, displayed formulas,
witnesses and original references survive; one proof gains an explicit
short-path case. Authors and the complete preamble are unchanged. Source
checks pass. The built-in compiler failed before TeX; no new PDF is verified.

The exact 012301 share-16 interpretation is prepared in 105 modules;
3 have accepted receipts at this checkpoint. Read the semantic progress
record for the remaining work. The pilot covers encoded input, data and counter structure; all 102
concrete clause checks remain pending.
The immediate target is this local theorem,
with the 012032 and 012340 requirements retained jointly. The completed
1,397-module 012310 count proof must not be restarted.

Maintained interval 191--235, contributor rebuild caveat and conditional 234
premises are unchanged. The optimum and 196 remain unresolved. Goal ACTIVE.
Read [the complete checkpoint](../milestones/146-initial-tree-and-paper/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next scheduled full revision: 156.

## Earlier record

# Research update: milestone 145

The separate count-sum proof is now complete: all 1,397 modules passed,
including the theorem that the five internal counts of every fitting
canonical 012310 window sum to at least 19. A fresh audit verified the
recorded sources, objects, logs and dependencies. Exact successful receipts,
source snapshots and checker snapshots are archived in three verified parts.
This discharges one local premise and gives no new global bound by itself.

Two saved cycles force comparison at least 235+95/2348 even after both
012301 and 012340 share floors are raised to16, with arbitrary existing
uniform occurrence credit and 012034 floor. Other weights and the graph
remain fixed. Lean checks this obstruction and 325F+159G>9074 as a necessary
joint-floor condition. The 012032 share 16 target must also be addressed for
the proposed three-floor combination; it adds 57 to the eleven-cycle.

The saved 012301 certificate passed complete independent replay: 285541
deductions, 31017505 references, 12977 original core inputs. Actual-snake
Lean interpretation remains pending. All 104 initial-tree parts passed their
truth-transfer checks, but the full assembly timed out. No local share 16
or share 18 theorem, and no new global bound, is claimed.

Read [the complete checkpoint](../milestones/145-countfree-012301/MATHEMATICAL_NOTE.md).
Goal ACTIVE. Next split the initial-database proof into smaller checked
pieces, then reuse the verified 012301 certificate. Paper145 preserves
authors and preamble; full rewrite remains due146. Compilation status is
recorded separately from source checks.

## Earlier record

# Research update: milestone 144

A retained fourteen-cycle has no012034 suffix and no occurrence-credit event.
Its fixed mean3445/7 forces comparison at least235+341/6569. Lean checks the
implication; independent source-row audits check the concrete cycle. Therefore
changing only012034 share and the existing uniform credit cannot reach234.
The two full-graph tests return235+12510/51599 and235+26297/98535.

The012034 share18 native certificate passed independent replay:145215
deductions and14710881 hints. Actual-snake Lean proof remains incomplete.
Six original modules passed; memory failure stopped the batch. A literal
initial database passes a6006-hint prefix, but its truth bridge remains open.

Next prioritise012301 share16, which affects the new cycle;012340 share16
and012032 share16 remain relevant distinct dependencies. Read
[the complete checkpoint](../milestones/144-countfree-share18/MATHEMATICAL_NOTE.md)
and the machine-readable next task. No new global bound. Goal ACTIVE.
Paper144 preserves authors/preamble and adds no definitions. Source checks
pass; built-in PDF compilation fails before TeX. Full rewrite remains due146.

## Earlier record

# Research update: milestone 143

A nine-cycle and its five-edge subwalk rule out012034 share floors at most14
for this comparison, even with an optimal potential and any nonnegative
uniform occurrence credit. Lean checks the lower comparison235+57/21124.
Floor15 survives this cycle test only; no full-graph sufficiency follows.
Next target the existing count-free share18 requirement in a separatecap17
query. The retained conditional comparison551765/2348 is unchanged.

The weaker share13 Boolean contradiction passed two complete replays:
29165 deductions,1699457 hints. Its231-module Lean export is preserved;
23 passed before intentional termination when the range obstruction
superseded13. No actual share13 theorem is claimed. Old share20 untouched.
Read milestones/143-countfree-share13/MATHEMATICAL_NOTE.md and its stop record.

Seven new Lean arithmetic reports passed. Maintained interval191–235
unchanged; other hypotheses and actual-snake assembly remain. Paper143
adds no definitions; source checks pass, PDF unavailable. Separate115
observed live at1203/1397; no143 job running. Goal ACTIVE, round is progress.

## Earlier record

# Research update: milestone 142

Uniform credit533/12 failed: completed-share mean4406/9 and range5377/9
give comparison9940859/42206>235. A nine-edge cycle has zero credited
events. Lean checks that its mean cap prevents this uniform-credit method
from crossing235, even with zero credit cost and zero potential range.
The all-edge evaluator and bounded independent result review passed.

Next investigate one empty-square claim: count-free012034 share at least13
in the existing scale12 units. It is the smallest integer floor removing
this particular cycle's zero-cost/zero-range obstruction; no global bound
follows from that alone. Floor18 remains the requirement in the retained
additional-share profile, whose comparison551765/2348<235 is unchanged.
Use a separate cap12 proof attempt and preserve the old share20 replay.

Read milestones/142-retuned-occurrence-credit/MATHEMATICAL_NOTE.md and
data/share-targets.json. Ten Lean arithmetic statements passed. Full
graph-to-snake assembly and inherited hypotheses remain. Maintained
interval191–235 unchanged; no new unconditional global bound. Paper142
adds no definitions; source checks pass, PDF unavailable. The separate115
batch was observed live at1158/1397. Goal ACTIVE; this round is progress.

## Earlier record

# Research update: milestone 141

The zero-credit graph test completed. The checked five-count exclusion removes
200 edges;4,661,572 remain. Completed-share mean3424/7 and range4159/7 give
comparison7724271/32824>235. Additional-share mean496 and range602 give
551765/2348=235-15/2348<235, recovering the conditional integer comparison234.
No new unconditional upper bound is established; both profiles retain their
inherited count assumptions and graph-to-snake obligations.

All-edge checks passed in the evaluator. Independent saved-result review
checked221 original rows, all new deletions, cycles, potentials and arithmetic.
Lean checked eight arithmetic statements, including the integer consequences
and next parameter. A full finite-potential Lean proof remains separate.

Next use credit533/12 on the completed-share profile: the new seven-cycle
and surviving zero-event18-cycle meet at mean3011/6. A potential range below
5341/6 would suffice for comparison<235. Retain zero credit for the additional
profile. Read milestones/141-zero-credit-comparison/MATHEMATICAL_NOTE.md.

The maintained interval is191–235, with incomplete independent rebuilding
of the contributor upper proof. Paper update141 adds no definitions;
source checks pass, PDF unavailable. The separate115 batch was observed
live at1127/1397. Goal ACTIVE; this round is progress.

## Earlier record

# Research update: milestone 140

Lean checked a new local restriction: a canonical012032 window whose first,
third and fifth internal counts are3,4,3 must have its second or fourth count
at least6. This applies to arbitrary snakes in Q9, either parity, with no
endpoint-location assumption. The actual-window proof closure has123 modules.
The separate zero-credit arithmetic has also passed Lean.

The restriction deletes the saved completed four- and five-cycles. It leaves
the additional-share six-cycle intact. No new graph minimum or global bound
has yet been established. Next test zero occurrence credit on the strengthened
graph, evaluating both profiles. At mean496, a potential range below632
would make the comparison below235; the old range602 is for different weights.
Read milestones/140-five-cycle-window/MATHEMATICAL_NOTE.md and the proof record.

The maintained interval remains191–235 with the documented upper-proof
rebuild limitation. The paper has a targeted update140 and no new definitions.
The separate115 job has a process-backed observation in this milestone.
Goal ACTIVE; previous turn and this round both made concrete progress.

## Earlier record

# Research update: milestone139

The combined exclusion and uniform-credit graph calculation completed.
Means2446/5 and496 are attained by new five- and six-edge cycles with zero
credited events. Both credit83/3 comparisons remain above235. Independent
saved-result review passed. Lean checked the counted-suffix allowance24
and the resulting obstruction for every nonnegative uniform credit.
Even the completed two-cycle arithmetic relaxation has optimum
2757328/11723>235. This fixed credit route cannot supply the next integer
improvement; inherited local hypotheses and graph assembly remain pending.

Next: bounded feasibility test for012032 with exact counts(3,5,4,5,3).
None of135 saved snakes matches it. The maintained interval remains191–235.
Read milestones/139-exclusion-occurrence-credit/MATHEMATICAL_NOTE.md.
Paper update139 adds no definitions; source checks pass, PDF unavailable.
The separate115 batch was observed live at1056/1397. Goal ACTIVE.

## Earlier record

# Research update: milestone 138

A complete Lean proof excludes the canonical nine-transition row012301430
with counts(>=6,3,3,3,5,2) at positions3–8, for arbitrary snakes and either
parity. This removes the recorded competing seven-edge cycle. Deletion alone
leaves the completed four-cycle and mean488. No new global length bound:
the maintained interval remains191–235 with the documented upper-proof
rebuild limitation.

Next combine the proved exclusion with the24-window allowance. The first
exact graph test is suffix credit83/3; target mean3011/6 and range<7753/6.
The arithmetic is checked; the required potential is unproved. The stronger
six-transition cap exclusion has independent proof replay only. See
milestones/138-seven-cycle-endpoints/MATHEMATICAL_NOTE.md and its checkpoint.

The existing paper was updated without new definitions; authors and preamble
are unchanged. Source checks pass, but the PDF compiler failed before TeX.
Last full revision136; targeted138; next full146. The separate115 batch was
observed live at1017/1397. The research goal remains ACTIVE.

## Earlier record

# Research update: milestone 137

The complete actual-snake bound of twenty-four low-pair windows passed Lean.
Any finite set of fitting canonical 012032 starts with relevant pair sum at
most nine has size at most 24, allowing overlap and either length parity.
The checked per-endpoint count is 12 under the unselected-common-neighbour
assignment. Nine modules and 23 theorem reports passed; the final source
also received an independent mathematical and scope review.

The proof constructs actual blocks, counts the exceptional prefix once,
subtracts actual missing pairs from capacity, sums degrees with repeated
labels allowed, and excludes both exceptional parameter cases. The previous
total 32 is improved to 24. The boundary-free count eleven, arbitrary distance-only assignment,
sharpness and a new global length bound remain unresolved.

The paper received a targeted update 137 with the completed proof. No named
definition was added. Its authors and complete preamble are unchanged, and
both saved copies match. Source checks pass; the built-in compiler failed
before TeX in its Windows helper. The updated PDF and layout are unverified.
Last full revision 136; next full revision 146.

The maintained interval is 191–235, with incomplete independent rebuilding of
the contributor upper proof. The optimum and 196 remain open. The uniform
credit obstruction persists even with an allowance of two events. Next:
investigate a necessary endpoint condition on the other seven-edge cycle,
which has no 012032 event. Read milestones131–132 and the new137 note before
setting a bounded local counterexample query. Retain all model assumptions.

At the saved process observation, the separate milestone115 certificate job
was live at 952/1397 modules. Check its command before any restart. The current
checkpoint is progress toward the active research goal, not completion.

## Earlier record

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

# Current mathematical status and continuation priorities

## Milestone 121 checkpoint

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

Earlier checkpoints below are historical snapshots.

## Milestone 120 checkpoint

For every six-transition window with canonical directions 012031, at least
one of the first, second, fourth and fifth internal singleton-square counts
is at least 4. The middle count is unrestricted. Lean checks the local
contradiction, its transfer to every actual snake, both graph orientations,
and three new reference-catalogue consequences. There are 26 checked modules
and 11 printed theorem-dependency audits. No new mathematical definition is used.

The original nine-transition target, edge 18806 with word 012031043, is
therefore excluded over its entire recorded count intervals. Weakening that
target exposed the shorter restriction. The selected proof has 5,956 deductions
and 344,241 hints; a separate encoder reconstruction and native replay agree.
Three more reference entries are discharged, taking the checked total to 15
and the remaining total from 1,366 to 1,363.

The graph experiment removes 63 additional transitions, including two edges
of the old conditional cycle. A replacement five-cycle preserves its mean
496 and potential range 602. The other profile retains mean 2915/6 and range
1730/3. Their integer comparisons remain 234 and 235, respectively. These
experiments inherit unresolved count-sum hypotheses and graph assembly work;
the new local theorem does not make either experiment unconditional.

The radius-three model admits a checked disconnected forest with counts
(4,4,13,4,4). The corresponding full-Q9 search remains UNKNOWN after 20 seconds
and 31 retained cycle cuts. Thus sharpness for actual snakes is unresolved.
All 131 saved bank paths pass 2,402,016 pair checks. Their 868 occurrences of
012031 have largest outer count at least 7. No replacement-cycle count tuple
occurs in that bank. These finite observations give no universal strengthening.

At the process-verified snapshot, batch 104 has checked 170/791 completed-profile
contexts and 167/791 conditional-profile contexts; batch 115 has checked
277/1397 modules. Both drivers remain active and unchanged. Their final proofs
are pending. The maintained interval remains 191 through 235 edges, supported
by the contributor proof and archived audit for 235; its complete independent
rebuild remains pending. Conditional 234, the optimum and the value 196 remain
unresolved. Paper revision 116 and both source copies are unchanged; the next
full paper revision is 126.

Earlier checkpoints below are historical snapshots.

## Milestone 119 checkpoint

A complete 148-edge snake contains a 012304 window with singleton counts
(3,6,3,4,6). Its total 22 disproves the proposed lower bound 23, even with
the first, third and fourth counts at most 4 and the other two at least 6.
Lean checks the complete induced path, window directions, exact counts and
counterexample. Nine axiom reports pass in 36.656 seconds. No mathematical
terminology was introduced, and no new long-snake lower bound is claimed.

Four local probes give four independently checked local forests. Six full-cube
probes give three complete snakes, two native contradictions and one UNKNOWN.
The complete snakes have 148,148 and 144 edges. The last realizes the exact
critical tuple (4,6,2,4,6). Boundary relaxation is therefore insufficient to
explain every surviving low-count state.

The two full-cube contradictions support total at least 23 under the respective
bounds [2,6..21,2,3,6..21] and [2,6..21,4,2,6..21]. Plain and tagged encoders
produce identical formulas. Separate native replay checks 19264 and 43795
deductions with 2240349 and 5045692 hints. Both concrete Lean contradictions,
sum semantics and actual-snake transfers remain pending. Their exact proofs
are preserved locally and in four verified transport archives.

The oriented 13-rule experiment reproduces the 117 removal set and both full
weight vectors before applying the new rules. They add credit on 449 and 446
suffix keys and remove no edges. Replacement cycles preserve both means and
ranges: 2915/6 with 1730/3, and 496 with 602. Integer comparisons remain 235 and 234.
All-edge potential inequalities were checked by the producer; the independent
review checks saved cycles, orientations, potential bytes and arithmetic.

The replacement cycles have no common five-centre direction shape. The next
single test is the full nine-transition word 012031043 from edge 18806, with
all six recorded counts constrained simultaneously and no extra sum cap.

At the process-verified snapshot,104 reports 162/791 contexts in each profile;
115 reports 232/1397 checked modules. Both drivers remain active and unchanged.
Their final assemblies remain pending. The maintained interval remains 191
through 235 edges, with the contributor proof and archived audit for 235 and its
complete independent rebuild pending. Conditional 234 and the optimum remain
unresolved. There are 1366 pending reference entries. Paper revision 116 is
unchanged; the next full revision is 126.

Earlier checkpoints below are historical snapshots.

## Milestone 118 checkpoint

The proposed outer-four lower bound 13 on 012301 fails in the radius-four
local model. Two verified forests have counts (4,2,10,2,3) and (4,2,10,4,2),
clipping exactly to the completed and conditional cycle tuples from 117.
They have seven and four components. These are local counterexamples;
no complete-snake counterexample or extension is established.

Fourteen bounded attempts cover twelve distinct cases: ten positive local
witnesses and four UNKNOWN results. The unrestricted total18 witness has
counts (3,2,5,4,4); the middle-at-least6 total19 witness is (4,3,6,2,4).
Thus unrestricted total at least19 and middle-at-least6 total at least20
also fail locally. Total at most17, and middle-at-least6 total at most18,
remain UNKNOWN after preserving and extending their saved cycle cuts.

Even granting the remaining candidate bounds 18 and 19, the old cycles survive.
Their maximum means under the shared coefficient budget are 977/2 and 504.
Both are too small to improve their corresponding integer comparisons,
even at zero potential range. These are ceilings from retained cycles,
not newly attained whole-graph minimum means. No new rule was accepted,
no full graph optimisation was run, and no numerical bound improved.

Lean checks the exact counts and disjoint induced path components of both
critical forests, plus five coefficient and comparison deductions. Nine
axiom reports pass. Radius-four identification and interior endpoint counts
are independently checked in Python. The first broader Lean attempt timed
out after 120.438 seconds; its exact source, checker and log are retained.
The split check passed in 30.735 seconds. No new mathematical terminology
or paper definition was introduced; four private constants store reused
concrete vertex data in the Lean source.

At the process-verified checkpoint, 104 reports 157/791 contexts in each
profile and 115 reports 193/1397 modules. Both drivers remain live; neither
was restarted or edited. Final potential assembly and the 115 actual-snake
theorem remain pending. The 117 local count contradiction still awaits
concrete Lean semantics and its full replay.

The maintained interval remains 191 through 235 edges, with contributor
proof and archived audit for 235 and its complete independent rebuild
pending. Conditional 234 and the exact optimum remain unresolved. The
reference union still has 1366 pending entries. Paper revision 116 and
both source copies are unchanged; the next full revision is 126.

Earlier checkpoints below are historical snapshots.

## Milestone 117 checkpoint

The new candidate on 012034 states that a middle count at most 5 forces
the outer four counts to sum to at least 16. Both previous attaining cycles
violate it. A complete native contradiction passes independent replay.
The reduced proof has 142,180 deductions and 8,712,029 hints, using 1,709
variables. Its 5,114 used clauses map exactly into the original formula.
The earlier proof is preserved. Concrete sum semantics and the full Lean
contradiction remain pending.

Lean checks the actual-snake transfer with that local contradiction as an
explicit hypothesis, plus two comparison deductions. One module and three
standard axiom reports pass. No mathematical definition was added. The first
attempt launched no compiler because the memory gate was closed; the waited
retry passed. Both attempt records remain saved.

The new rule removes 23,285 further graph edges. The completed-floor mean
increases from 6309/13 to 2915/6, with range 1730/3 and comparison 1324108/5623.
The conditional-floor mean/range remains 496/602. Integer comparisons remain
235 and 234. Both experiments assume unproved local rules. Independent
saved-cycle and potential audits pass; the producer supplies the all-edge
lower certificates.

All applicable deficits vanish on the replacement 18-edge and 3-edge cycles.
Changing coefficients within this eleven-rule family cannot improve their
mean ceilings. Range reduction alone also cannot improve the integer bounds.
The next shared target is 012301, with exact outer sums 11 and 12 and middle
count in [6,21]. An outer lower bound 13 remains an untested candidate.

The independently checked local witness (5,3,5,3,6) has outer sum 17 and five
components. It is not a complete snake. Outer sum at most 16, unrestricted
total at most 20, and total at most 20 with all counts at most 5 remain UNKNOWN
in bounded runs. The candidate lower bound 16 is not shown sharp.

At this process-verified snapshot, milestone 104 reports
152/791 completed-profile and 153/791 conditional-profile contexts;
milestone 115 reports 159/1397 checked modules. Both drivers are live.
Their final certificates and the 012310 actual theorem remain pending.
Neither batch was restarted or changed.

The maintained interval remains 191 through 235 edges, with the contributor
proof and archived audit for 235 and its complete independent rebuild pending.
Conditional 234, the optimum and 196 remain unresolved. There are 1,366
outstanding reference entries. Paper revision 116 is unchanged; next revision 126.

Earlier checkpoints below are historical snapshots.

## Milestone 116 checkpoint

The paper is revised through milestone 115, with no new definitions. Its
single named definition is the problem itself. All 135 previous statement
blocks, author metadata, hyperlink settings and appendices are preserved.
Three statement blocks collect checked count restrictions and the shared
excess budget. All 13 printed snakes pass 118,673 pairwise adjacency checks.
Nine reused module receipts, their exact source/object/log bytes and 47
printed axiom reports were checked. No new Lean compiler was launched.

The new local results include the 012340 three-count restriction and the
012314 theorem: middle count at most 2 forces the outer four counts to sum
to at least 19. The paper states their proofs using ordinary count notation.
Twelve of the 1,378 reference entries are discharged; 1,366 remain.

The expanded count-sum family is explicitly conditional. Its finite means
6309/13 and 496 retain integer comparisons 235 and 234. The final attaining
cycles contain no 012345 window, so strengthening only that rule to total
at least 23 leaves their weights and the exact means unchanged. The 23
candidate has native negative evidence and a six-component local equality
witness, without a checked negative certificate or a complete-snake witness.

At this process-verified observation, milestone 104 has
148/791 completed-profile and 147/791 conditional-profile
contexts checked. Milestone 115 has 123/1397 modules checked. Both
drivers remain active; full certificates and the 012310 actual theorem are
pending. Exact partial receipts and logs are archived in this milestone.

The built-in compiler failed before TeX processing because its Windows
helper could not prepare the preview. No new PDF or page layout is verified.
The maintained interval remains 191 through 235 edges, with the archived
contributor proof and pending complete independent rebuild. Conditional
234, the optimum and 196 remain unresolved. The next full paper revision
is scheduled for milestone 126.

Earlier checkpoints below are historical snapshots.

## Milestone 115 checkpoint

Milestone 115 reduces the 012310 native certificate to 287,753 deductions
and 16,816,989 propagation hints, and checks its concrete interpretation
in Lean. The complete native export passes simulation. Its sequential
Lean batch has 50/1397 checked modules in this process-verified
snapshot; the full contradiction and final actual-snake theorem remain pending.

The new candidate is that five internal counts sum to at least 23 when
the six consecutive directions are distinct. Native tests reject totals
at most 22 after five validated cycle cuts; a verified six-component local
forest attains 23. The negative certificate and complete-snake sharpness
remain unresolved. Simpler end-cap restrictions have explicit local controls.

The final graph means are 6309/13 and 496, with valid ranges 7656/13 and 602.
Integer comparisons remain 235 and conditional 234. The attaining cycles
contain no 012345 window at either placement, so further strengthening
that rule leaves the means unchanged by monotonicity. Even zero potential
range cannot improve these integers at the present means.

The maintained interval remains 191 through 235 edges, with the contributor
evidence and complete independent rebuild obligation preserved. Milestone 104
also remains live. This is a dated snapshot, not permission to restart either
batch. Paper revision 106 is unchanged; full revision 116 is due next.

Earlier checkpoints below are historical snapshots.

## Milestone 114 checkpoint

The native contradiction for five-count total at most 18 on canonical
012310 has been independently replayed in both core and original-CNF
identifier systems. It uses 5,206 input clauses, 358,464 deductions and
22,088,504 propagation hints. Its concrete counter interpretation and
full Lean replay remain pending. Lean checks the conditional geometric
transfer and three exact comparison lemmas: two modules, four standard
axiom reports, and no new mathematical definitions.

The nine-rule finite experiment removes 2,263 further keys beyond 113,
retaining 4,865,603. Its completed-floor mean rises to 2424/5 with range 2881/5;
comparison 5517073/23424 retains integer 235. The conditional profile remains
496/602 and integer 234. A stronger total-20 hypothesis has an UNKNOWN
local probe, lowers only the first range to 565, and retains both integers.
Zero-deficit cycles fix coefficient ceilings 2424/5 and 496 in these families.
Both profiles continue to assume other unproved local rules.

The selected proof completed in 20.656 seconds using temporary storage,
after the same formula/options timed out at 60 seconds on the research
volume. Their first 40,935,424 proof bytes agree. Reusing 115 valid cycle
cuts produced a larger retained proof and was not selected. Preserve all
attempts and the independently replayed original certificate.

The next priority is reducing that certificate before concrete Lean
export. The subsequent common local target is 012345, with exact tuples
(4,3,3,5,4), (5,4,2,5,5), and (5,4,3,4,5). A middle count at most 3
and total at most 21 remains an untested combination.

Milestone 104 resumed after its unchanged interrupted module passed on
retry. This process-verified snapshot records 105/791 completed
and 104/791 conditional contexts, with active module
`ConditionalBatch104G086`. Preserve the running batch. The reference
union still has 1,366 unresolved entries. No new global upper bound is
established; the maintained interval is 191 through 235 edges with the
full independent rebuild pending. Conditional 234 and the optimum remain
unresolved. Paper revision 106 is unchanged; next full revision 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 113 checkpoint

On canonical 012034, central caps (5,4,5) appear to force the outer
pair to sum to at least 9. Native UNSAT supports the candidate, but two
30-second proof-generation attempts timed out. Lean checks the geometric
transfer with the local contradiction retained as an explicit premise.
No concrete actual-snake pair inequality is claimed.

Lean also checks that the pair deficit fits the existing shared maximum
credit with capacity 4*a+b<=120. There are two successful modules, four
standard axiom reports and no new mathematical definitions. Eleven local
tests comprise six native UNSAT results, two UNKNOWN results and three
independently verified local witnesses. The witness (6,5,4,5,3) attains
pair sum 9, so the current relaxed assumptions cannot force 10.

The pair hypothesis removes 41,361 further keys beyond milestone 112,
leaving 4,867,866. Both finite comparisons remain unchanged: completed
mean/range 484/557 gives 1103389/4684, with integer floor 235; conditional
496/602 gives 551765/2348, with floor 234. Both assume unproved sum rules.
Replacement cycles have zero applicable deficits, proving coefficient
ceilings 484/496 within this fixed eight-rule family. No new global
numerical snake bound follows.

Both replacement cycles contain a 012310 window with five-count sum 18.
The next bounded test is total at most 18 on that pattern with no extra
count caps. A total lower bound of 19 would remove these cycles; compare
both full profiles to determine whether other attaining cycles survive.

At this saved process-verified observation, milestone 104 was RUNNING with
95/791 completed and 94/791 conditional contexts
checked. Its active module was `CompletedBatch104G081`. Preserve
that batch and all immutable evidence. The reference union still has
1,366 unresolved entries.

The maintained interval remains 191 through 235 edges, based on the
contributor proof and archived audit, with a full independent rebuild
pending. Conditional 234, the exact optimum and 196 remain unresolved.
Paper revision 106 is unchanged; the next full revision is 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 112 checkpoint

A new actual-snake theorem proves that on canonical direction pattern
012314, middle count at most 2 forces the four outer counts to sum to at
least 19. The concrete counter semantics, complete contradiction and
geometric transfer pass Lean without a collective catalogue premise.
The proof uses 3,306 clauses, 7,020 deductions and 367,588 hints after
a verified permutation of 1,718 active variables. Independent replay
and reconstruction pass. This round has 40 successful modules and 20
printed standard axiom reports, with no new mathematical definitions.

Lean also checks a shared budget for outer-four and total-five deficits.
Fixed coefficients satisfy 4*a+b<=120; take the maximum of the weighted
alternative deficits. The clipped-count boundary contribution remains
21, or 2,520 after scaling. Actual local lower bounds remain explicit
hypotheses in the generic budget theorem.

The final seven-rule conditional experiment leaves 4,909,227 graph keys.
Balanced coefficients (24,24) give completed mean 484/range 557 and
comparison 1103389/4684, with integer floor 235. The conditional profile
retains mean 496/range 602 and floor 234. Surviving zero-deficit cycles
show these means are ceilings for every nonnegative coefficient choice
within the fixed family. Balanced coefficients attain both ceilings.
Lean-checked arithmetic shows that smaller nonnegative potential ranges
alone cannot exclude 235 or 234 at these slopes.

Six local witnesses independently rule out other strengthenings within
the relaxed radius-four model; they are not complete snakes. The next
useful target is the all-4 configuration on 012034, followed by a broader
count-sum inequality if it is impossible. The relevant stronger sum
probes are UNKNOWN. The separate 30-second proof-generation timeout is
preserved; its partial LRAT is not a checked certificate.

At the saved process-verified observation, milestone 104 was RUNNING with
83/791 completed and 82/791 conditional contexts
checked. Its active module was `ConditionalBatch104G072`. Preserve
that batch. The reference union still has 1,366 unresolved entries.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit with full independent rebuilding
pending. Other sum hypotheses, graph-oriented guards and complete global
integration remain pending. No improved numerical snake bound is claimed.
Conditional 234, the exact optimum and 196 remain unresolved. Paper
revision 106 is unchanged; the next full revision is 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 111 checkpoint

For canonical directions 012340, a new checked theorem requires the
second internal count to be at least 4, the third at least 3, or the
fourth at least 6. The outer two counts are unrestricted. The local
contradiction, actual-snake transfer and both graph orientations pass
Lean. There are 58 successful module records and 13 standard axiom
reports. The main contradiction has 2,040 clauses, 11,711 deductions
and 611,907 hints; independent replay passes. No mathematical definition
was introduced.

This restriction removes 1,462 additional graph keys beyond milestone
110, leaving 4,942,589. Its integer comparisons remain 235 and conditional
234. Four independently checked local witnesses rule out several stronger
local claims; their relaxed boundaries and multiple components prevent
interpreting them as complete snakes.

The proposed outer-sum lower bounds are 22 when the middle count is at
most 2, 19 when it is at most 3, and 17 without a middle restriction.
The sum-22 case has a complete native sorted-input contradiction with
71,388 deductions and 6,105,267 hints, independently reconstructed and
replayed. Concrete sum semantics, Lean replay and actual-snake transfer
remain pending. The generic counter-soundness helper is checked. The
two other sum cases have native UNSAT records without checked certificates.
Sorting retains all 84 literal occurrences, including seven duplicates.

Assuming all three sum bounds and their common coefficient-30 excess
argument removes 7,999 more graph keys, leaving 4,934,590. The completed
mean improves from 483 to 3384/7, with potential range 3860/7 and exact
comparison 1930913/8196. Its integer floor remains 235. A fourteen-edge
cycle attains the new mean. The conditional profile retains mean 496,
range 602 and floor 234. Every edge inequality was checked by the native
calculation; complete Lean graph certificates and the excess-budget
integration remain outstanding.

At the saved process-verified observation, milestone 104 was RUNNING with
71/791 completed and 70/791 conditional contexts
checked. Its active module was `ConditionalBatch104G061`. Preserve
that running batch. The reference union still has 1,366 unresolved entries.

The maintained range remains 191 through 235 edges, based on the
contributor proof and archived audit with a complete independent rebuild
pending. Conditional 234, the exact optimum and 196 remain unresolved.
Paper revision 106 is unchanged; the next full revision is 116. Large
proof artifacts have verified gzip archives, with raw originals retained
locally. Failed proof attempts preserve their original timeout status.

Earlier checkpoint sections below are historical snapshots.

## Milestone 110 checkpoint

A new checked restriction excludes counts (5,5,2,4,5) on canonical
six-transition direction window 012340. Lean checks the local clause
semantics, contradiction, actual-snake statement, and both graph orientations.
Sixty-five modules pass, with six printed axiom reports. The proof has
1,664 input clauses, 2,007 deductions and 177,364 hints; independent RUP
replay also passes. No new mathematical definition was introduced.

The theorem removes 865 additional keys beyond milestone 109's 2,092,
leaving 4,944,051. It breaks the previously displayed completed-profile
cycle, but a different cycle keeps the mean 483 and range 551. The
conditional profile remains mean 496 and range 602. Assuming all seven
proposed exclusions removes 4,773 additional keys, with the same comparisons.
All seven native count probes reported UNSAT; edge 2139224 needed three
cycle cuts. Only edge 3534483 has a checked theorem in this round.

The scan of all 143 older proof roots found no relaxed candidate hitting
the original limiting cycles. Hypothetical share floors 76 on the seven
patterns also leave both comparisons unchanged. The next priority is a
restriction covering a family of surviving count patterns; test both full
profiles before investing in further isolated certificates.

At the saved process-verified observation, milestone 104 was RUNNING with
55/791 completed and 55/791 conditional contexts
checked; its active module was ConditionalBatch104G046. The running
batch and original graph were left intact. The reference union still has
1,366 unresolved entries, after the twelve checked in earlier milestones.

The maintained interval remains 191 through 235 edges, based on the
contributor proof and archived audit with its full independent rebuild
pending. Conditional 234 remains unresolved. The exact optimum and 196
remain open. Paper revision 106 is unchanged; the next full revision is 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 109 checkpoint

For five consecutive distinct transition directions, a new checked
restriction requires the first singleton-square count to be at least 2,
the second to be at least 6, or the fourth to be at least 3. The third is
unrestricted. The 441-clause core has 270 regenerated deductions and 1,343
hints. Lean checks the relaxed semantics and its actual-snake application.

Exact enumeration excludes 2,092 of 4,947,008 accepted full graph keys.
The separate restricted experiment has 4,944,916 keys. Both sharp cycles
survive: the profiles remain at mean 483/range 551 and mean 496/range 602.
All five one-unit floor obstructions survive. All sixteen screened relaxed
boxes miss both sharp cycles. Lean also checks that even range zero cannot
improve either integer comparison while the respective mean survives.

Twelve exact reference entries are now checked. Lean proves the full union
equivalent to the filtered assertion for 1,366 remaining entries. Ten final
modules and sixteen printed axiom reports pass. No mathematical definition
was added. The native graph computations remain separately labelled evidence.

At the immutable process-verified observation, milestone 104 was RUNNING with
42/791 completed-profile contexts and 41/791
conditional-profile contexts checked. Its active module was CompletedBatch104G038.
The active original graph, checker and generator remain unchanged.

The maintained interval remains 191 through 235 edges. The contributor proof
and archived audit support 235, with a complete independent rebuild pending.
Conditional 234 still needs the remaining reference union, complete graph
certificates and five local floors (16,18,16,16,16). The exact optimum and
conjecture 196 remain open. Paper revision 106 is unchanged; next revision 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 108 checkpoint

Lean now excludes the simultaneous singleton-count bounds 2,2,3 at
the first, fourth and fifth internal centres of direction word 012304.
The second and third counts may range from 0 through 21. Six unused counter
limits were relaxed while preserving the 120 raw clauses and their variable
meanings. A regenerated contradiction has 75 deductions and 426 antecedent
references, independently checked as plain-clause RUP and through Lean.

A checked bounds-containment argument supplies seven exact catalogue entries.
Together with milestone 107's first entry, indices 0,472,495,535,572,602,619,620
are discharged. Lean proves equivalence between the full catalogue assertion
and the filtered assertion for 1,370 remaining entries. Nine final modules
and fifteen axiom reports pass. No new mathematical definitions were added.

The failed first coverage attempt and successful repair are preserved. The
repair uses the existing computable centre-list equality before finite checks.
Shared dependencies were reused; a clean independent rebuild is not asserted.
The three source reviews and final proof audit agree on the scope.

At the immutable process-verified observation, milestone 104 was RUNNING with
34/791 completed-profile contexts and 33/791
conditional-profile contexts checked. Its active module was ConditionalBatch104G029.
Consult its live record for later progress. Its active files were unchanged.

The maintained interval remains 191 through 235 edges, with the contributor
proof and archived audit supporting 235 and its complete independent rebuild
pending. Conditional 234 still requires the remaining reference entries,
complete graph certificates and five local floors (16,18,16,16,16). The exact
optimum and conjecture 196 remain open. Paper revision 106 is unchanged;
the next full revision is scheduled for 116.

Earlier checkpoint sections below are historical snapshots.

## Milestone 107 checkpoint

The first exact reference key, directions 012 and singleton symbols (1,1),
has a recovered closed Lean refutation. The original 1,172-clause semantic
input matches the archived source. A fresh LRAT certificate has 968 lemmas
and 41,184 hints, independently checked as plain-clause RUP and through seven
Lean segments. The final isolated replay has 19 checked modules and 14
standard-axiom reports. No new mathematical definitions were added.

Lean proves that the full reference-union assertion is equivalent to the
assertion for its remaining 1,377 entries. The first failed combined import
attempt is preserved; the successful attempt changes only recovered import
paths to avoid shadowing shared modules. Existing support objects are reused.
This is recovery of an established restriction, with no new numerical bound.

An independent source audit identifies 143 exact older D alternatives,
including the recovered first entry. The next representative is union index
472, with a recorded 120-clause core; its decoded clauses match the archive.
The alternative-root correspondence supplies no unperformed proof replay.

At the immutable process-verified observation, milestone 104 was RUNNING with
27/791 completed-profile contexts and 27/791
conditional-profile contexts checked. Its active module was
CompletedBatch104G024. Consult the live record for later progress.

The maintained interval is 191 through 235 edges. The contributor upper bound
retains its archived audit and pending independent rebuild. The remaining
reference entries, complete graph certificates and five conditional shares
remain distinct requirements. Paper revision 106 is unchanged; the next full
revision is scheduled for 116. The exact optimum and conjecture 196 remain open.

The current remaining-reference premise is the tail of the exact list.
Earlier checkpoint sections below are historical snapshots.

## Milestone 106 checkpoint

The manuscript now presents the checked graph coverage, complete actual
weight interpretation and exact 1,378-key reference-union implication. Its
conditional 234 route uses pending floors (16,18,16,16,16), slope 496 and range 602.
The earlier floor 20/range 600 optimality result is kept separate. No smaller
unconditional numerical bound is claimed.

Named definitions were reduced from three to one, with no new definitions.
The source preserves all authors, hyperlink settings, appendices and printed
witnesses. All 13 snakes pass 118,673 pair checks. There are 135 statement blocks:
130 prior blocks are unchanged, two propositions are strengthened using checked
results, two definition environments become prose, and three deductions are
added from existing evidence. This milestone ran no new Lean compiler.

The built-in compiler failed before processing TeX because its Windows helper
could not enforce the required writable roots. No current PDF or visual layout
is verified. The exact diagnostic is saved.

At the saved process-verified observation, milestone 104 was RUNNING with
21/791 completed-profile contexts and 20/791
conditional-profile contexts checked. The recorded active module was
ConditionalBatch 104 G 017. This is a dated snapshot, not a live total.

The maintained interval remains 191 through 235 edges. The contributor 235 proof
retains its inspected source and archived audit; a complete independent rebuild
is pending. The reference refutations, full potential certificates and five
conditional share bounds remain separate obligations. The exact optimum and
conjecture 196 remain unresolved.

Earlier sections below retain their historical snapshots. The exact union is
the current reference premise, and paper revision 106 supersedes revision 96.

## Milestone 105 checkpoint

Five general theorems passed Lean with only propext, Classical.choice and
Quot.sound. No definitions were added. The new route assumes refutations for
the exact 1,378-pattern reference union, together with the unchanged complete
graph check and, for 234, the five local share premises. It does not prove
those remaining assumptions.

The source selection uses 1,378 of the 1,383 distinct roots in the full source
catalogues. All selected semantic sources are present in the pinned Git trees;
the generated refutation sources are absent there. This source audit supplies
no closed refutation.

Milestone104 remains active. The saved process-verified observation records
14 completed-profile and 14 conditional-profile
contexts checked. Read its local data/batch-progress.json for current progress.
The interval remains 191 through 235 edges, with 234 conditional.

The new exact-union premise supersedes the two-catalogue premise only in the
new theorem chain. Earlier checkpoint descriptions below are historical.

## Milestone 104 active batch

The complete sequential batch is active. At the saved snapshot, it has
7 completed-profile and 7 conditional-profile
contexts checked. These are snapshot counts, not a claim that the batch is
finished. Read `milestones/104-complete-potential-batch/data/batch-progress.json`
on the running machine, the [saved launch snapshot](../milestones/104-complete-potential-batch/data/start-checkpoint.json),
and [resumption notes](../milestones/104-complete-potential-batch/NEXT.md) before
starting any process. There are 1,157 proposed groups covering all 1,570
previously pending profile/context pairs. Both graph assemblies remain pending.

The general graph-assembly theorem has passed Lean and adds no definitions.
Milestone 103's joint traversal and four matched comparisons are saved and
pushed in commit 04f5fad09c3e6f36568b846050592662174327dc. The preferred methods
are baseline for the completed profile and joint traversal for the conditional
profile, with a separate alternative for timed-out groups. No new global
snake bound is claimed.

## Milestone 103 checkpoint

Lean checked the general implication from successful joint traversal to
the existing prefix checker. Both source and target digit schedules, the
rejected-branch rule and the potential-width checks are covered. There are
11 checked modules and 26 distinct theorem axiom audits.
Only two reusable implementation definitions were added: branch selection
and joint traversal. No mathematical terminology or manuscript definition was added.

Four matched sequential comparisons passed, including transfer to the
original full context checker:

| Profile | Direction/history | Baseline seconds | Joint seconds |
| --- | --- | ---: | ---: |
| completed | 99/37 | 58.703 | 83.422 |
| completed | 0/0 | 59.734 | 85.609 |
| conditional | 99/37 | 61.734 | 29.969 |
| conditional | 0/0 | 122.250 | 71.766 |

Each pair uses the same imports, weights, potential roots, clipping bound,
acceptance root and candidate codes. No other Lean compiler was active at
launch. These are end-to-end module times from one pair per profile and
context; unrelated system activity was not isolated. They do not establish
a universal performance ordering.

The provisional batch choices, based on total time for the two contexts in
each profile, are completed: baseline; conditional: joint.
The batch should preserve a fallback for a context that exceeds its limit.

These contexts were already certified. Coverage therefore remains six of
791 contexts per profile: 34,701 accepted edges for the completed profile
and 34,148 for the conditional profile. There are 785 contexts per profile
still pending. Comparisons do not add distinct graph coverage.

Prepare one resumable sequential batch for all remaining contexts, reusing the six existing certificates per profile. Reuse one verified reduced check per identical acceptance root, weight expression and potential-root pair, then prove each original context by the bounded transfer. Select the baseline or joint method from the measured evidence, with a fallback for timed-out contexts. Assemble the original complete-graph theorem only after every context and every missing block are covered. Do not start another series of isolated timing pilots.

## Result and evidence boundary

Length means edges. The maintained project interval is

\[
191\le a(9)\le235.
\]

The lower bound has an explicit checked witness. The upper bound uses the
inspected contributor theorem and saved audit; this continuation has not rebuilt
that entire proof independently. The exact optimum remains unresolved.
The conjecture 196 has neither a matching construction nor an optimality proof
in this work. The proposed improvement to 234 remains conditional.

The current paper is revision 96, by Iori Hironaka, Tommy Ma and Steven Zhan.
Its existing editor and repository sources both have SHA-256
`7d4d974bc353ca723e4a5362b0960610d959dfe622b115b629968818c178875c`.
The 134 statement blocks, 199 resolved labels, 55-row history table and all
printed witnesses pass source checks. The original appendix body and all
metadata are preserved. The compiler could not start before processing the
source. The next scheduled full paper revision is milestone 106.

## Chosen route: charge empty squares

Let a nontrivial snake have \(m\ge1\) edges and \(v=m+1\) vertices. Let \(T\) be the total
singleton-square count and \(s_0\) the number of empty squares. The accounting
identities and charge budget are

\[
T+2s_0+35v=9214,\qquad
\Sigma\le48s_0,\qquad
24T+\Sigma+840(m+1)\le221136.
\]

Here \(\Sigma\) is the sum of scale-12 empty-square shares. Combining the
five-centre window charges and the boundary contribution 21, for \(m\ge9\), gives

\[
W+4200m\le1098960.
\]

Milestone 97 also verifies the weaker profile with 012034 floor 18, keeping
the other eight original target floors fixed. Its potential has slope 496 and
range 602, giving $4696m\le1103530$ and conditional integer bound 234.
The least pending floor vector inside the original integer box is
$(16,18,16,16,16)$. The original stronger profile below remains valid as a
separate sufficient comparison with range 600.

The full proposed finite graph has 1,601,856 states and 4,947,008 edges. Its
recorded potential gives the conditional inequality

\[
496(m-8)\le W+600,
\]

so \(4696m\le1103528\). At \(m=235\), the left side exceeds the right side
by 32. This yields 234 only after every local premise, actual-snake graph
interpretation and complete potential check has been supplied.

Completed local shares, now including the checked 012310 share-12 theorem,
give mean 483 and potential range 551. The exact comparison is 157625/669,
with integer bound 235. Its weight and potential hashes match the earlier
comparison that assumed this lemma. The previous completed subset had mean 480
and range 536. These finite-model calculations do not independently replace
the contributor's global theorem; graph interpretation and Lean potential
replay remain required.

## Local share catalogue

The shapes below use canonical direction labels. The listed floor is the sum
of the five internal scale-12 shares, independently of their singleton counts.

| Shape | Target floor | Final target theorem status |
| --- | ---: | --- |
| 012031 | 16 | Checked, case7300 |
| 012032 | 16 | Pending, case7301 |
| 012034 | 18 suffices; original target 20 | Pending; case7302 retains the stopped target-20 replay |
| 012301 | 16 | Pending, case7303 |
| 012304 | 16 | Checked, case7304 |
| 012310 | 12 | Checked, including reversal, case7305 |
| 012314 | 16 | Checked, case7306 |
| 012340 | 16 | Pending, case7307 |
| 012345 | 16 | Pending stronger target, case7308; the weaker floor 12 is checked |

Case 7305 completed all 465 source modules and 100 printed theorem audits,
including geometry and reversal. Its selected sources and compact proof were
archived and restored byte-for-byte. No case7305 proof process remains active.
The combined catalogue passes 35 audits and retains exactly five local targets:
7301, 7302, 7303, 7307 and 7308. Earlier pending checkpoints remain historical evidence.

Milestone 83 prepared the case7302 target-20 proof. Its replay is currently stopped. All 121 semantic shards and
their combined interpretation passed, giving 127 modules before refutation
replay. The generated compact refutation, original export simulation and
reduced export simulations passed. Selected Lean replay and final geometry
remain pending. Inspect its saved checkpoint and actual
process before restarting anything.

Adding only this unproved floor gives exact finite mean 9259/19 and scaled
potential range 11301 at denominator 19. Its bound 20965613/89059 still
rounds down to 235. It raises 1,043,097 weights over the completed-share
model. All-edge checking and three Lean arithmetic audits do not discharge
the added local premise or the full graph interpretation.

## Earlier proof interfaces and development record

The following paragraphs preserve earlier milestone observations. Their
pending-job statements describe those snapshots. The milestone 103 checkpoint
above supersedes them: both 127-class batches and their assembly are complete;
case7302 is stopped. The remaining tasks are listed in NEXT_AGENT_PROMPT.md.

Milestone 75 supplies longest-suffix history recognition, credit lookup and
count coding. Milestone 77 supplies direction-table coverage and the numeric
history interface. Milestone 78 proves the actual numeric history update and
assembles the direction, history and counts into one consistently numbered
state sequence, with 29 theorem audits. A direction window uses the oriented table ordering:
132 eight-direction states and 505 nine-direction edges. Reversal classes are
different objects and cannot be used as these IDs.

For \(m\ge9\) and edge start \(r<m-8\), the six count symbols are at centres
\(r+3,\ldots,r+8\). The source retains the first five and the target the last
five. The entering count is at \(r+8\), and credited shares lie at centres
\(r+4,\ldots,r+8\). There are \(m-8\) direction edges and \(m-7\) shape states,
including the terminal state. Shorter paths already satisfy the intended upper
bound. Count symbol six means the interval \([6,21]\).

Milestone 79 adds 31 theorem audits. Its count-slice, digit, encoding-injectivity,
reversal and saturation results connect encoded graph tests to actual counts.
Every actual snake survives the ten completed milestone 72 interval filters,
at all three offsets and in both orientations. The closed local certificates
are imported from pinned existing objects, without a clean dependency rebuild.

Milestone 81 closes the forty recovered short-rule filters: 66 theorem audits
across eight modules, covering both orientations and every fitting represented
placement. A separate exact builder-loop comparison checks 23,561,280
direction/count pairs, with source reconstruction and complete input hashes.
It reuses 970 pinned certificate objects and freshly checks three small support
sources. It does not rebuild the entire inherited closure.

Milestone 84 closes all three history-exclusion guards, with 38 audits across
eight modules. The actual emitted IDs recover each unique eleven-direction
word, and its count lower bound three excludes the digit cap two. All three
count proofs and five small helper lemmas were checked afresh against the
current window bridge. An exact isolated-loop comparison covers all 37,875
history/direction pairs and all count codes for the three active guards.

Milestone 85 supplies the exact 1,378-key reference table: 1,287 keys from the
235 catalogue and 91 additional keys from the 236 catalogue. Twenty-seven
modules passed 103 Lean audits, including the full table and retention in
both orientations at every fitting offset. The final theorem retains the
two closed catalogue-refutation premises. The key data and their membership
proofs are checked; their closed refutation dependencies have not been imported
into the current local environment. A bounded provenance search and exact
source pins document this distinction. The isolated builder-filter comparison
agrees on all 23,561,280 direction/count pairs.

Milestone 87 adds 27 Lean theorem audits across four modules. It combines
all retention families, defines an executable bounded numeric predicate and
proves that every fitting actual snake step passes it under the same two
reference-catalogue premises. A retention cover contains every accepted key;
exact table equality is a stronger sufficient condition. Given finite coverage
and the two endpoint-column identities, the checked assembly assigns an
in-bounds saved edge to every step of the complete actual state walk.

Two independent executable audits verify exact accepted-code equality on all
36,904,896 compatible candidate keys, the 4,947,008 saved rows, their ordering
and every endpoint. All 791 compatible blocks match; all 37,084 incompatible
blocks are empty. Full candidate keys are unique, while 206,589 endpoint pairs
have multiplicity two. Keep edge identity as (direction, history, count code).
The Python checks do not discharge the concrete Lean coverage or endpoint
premises, and do not certify equality with the executable Lean predicate.
The 791 blocks share only 127 distinct count-code sets. A shared six-way
decision diagram with 3,981 nonterminal nodes reconstructs every set and
block exactly, occupying 29,924 compressed bytes. Milestone 88 supplies the generic coverage implication and one concrete
checked context; the complete finite certificate remains open.
The combined imports reuse hash-checked existing proof objects; no complete
dependency rebuild is claimed.

Milestone 88 adds 26 Lean theorem audits. A rejection box is a product of
six count intervals with a checked original-rule witness. A six-way coverage
tree proves that every vector is either accepted by a membership diagram or
contained in one of these boxes. The generic theorem proves numeric retention
implies diagram acceptance; its actual-snake specialization retains the two
reference-catalogue premises. The direction-0/history-0 pilot supplies the
finite premises: Lean checks all 375 witnesses, the coverage equation and the
resulting retained-code theorem. It has 723 distinct tree nodes and 6,123
accepted codes; the three concrete proof checks took 92.594 seconds.

The computational reconstruction still matches every saved block. Moreover,
all 127 membership classes have a common box cover available across every
context of that class. Pruning yields 82,659 class-box occurrences, compared
with 356,548 direct direction-box occurrences. This suggests 127 shared
geometric checks. Each context still needs its own rule witnesses; milestone 88 stored example
witnesses, and milestone 89 supplies every context-specific list. The full all-context Lean
certificate and identification with the saved full-key rows remain open.
These generic and pilot results do not give a new global bound.

Milestone 89 records 28 additional Lean theorem audits. History-free
witnesses transfer across bounded history IDs of the same direction. Shared
assembly pairs an equally long witness list with the fixed geometric box list,
including the three contexts whose history witness occupies position zero.
All 543,827 witness occurrences in 791 contexts have been materialized and
checked computationally, compressing to 211 aligned lists and 4,387 witness
constructors. Their complete concrete Lean validity equations remain open.

All 127 shared cover trees are generated and pointwise replayed on 5,925,312
class/code pairs. A balanced table lookup is proved equivalent to the original
list at every index and default. Its concrete graph table and the geometric
coverage equations for classes 0 and 1 pass Lean. The class-1 proof module took
51.828 seconds; earlier direct and array-box experiments were stopped without
completion after 685.187 and 475.312 seconds. These concurrent timings do not
give a controlled speed ratio. The sequential full-class batch is active in
tool session 23168; its frozen checkpoint covers only classes 0 and 1.

Case 7302's original replay stopped at Check66 after its 300-second limit. A
first resume failed while replacing a stale temporary output. Both attempts
are preserved. The unique-output resume, tool session 14427, uses a 900-second
limit and has passed Check66 in 130.02 seconds. It reuses unchanged proof
sources and completed modules. Inspect actual processes before any restart.
Final geometry, reversal and the local-share audit remain pending.

Milestone 90 adds 17 Lean theorem audits. Balanced lookups preserve the exact
505-direction and 1,378-reference tables, including out-of-range defaults.
The class-1 certificate now gives retained-code membership for directions
1, 3, 307, 308, 310 and 312, for every bounded history under the original
predicate. Its six assignments contain 3,840 witness checks, and the proof
module passed in 21.125 seconds, excluding data and shared table checks.

Compatibility and count conditions are separated by a checked general
identity. A normalized direction-pattern expression permits reference keys
with the same shape and count-list length to share the shape calculation.
Concrete compressed descriptors and their full assembly remain unchecked.
The computational plan has 507 base validity jobs and three history heads,
covering all 791 contexts. Its 357,823 entries contain 15,353 distinct shape
tests and 2,651 count tests, together with 508 outer and 2,329 catalogue
guards. Every saved direct/factored Boolean comparison passes. These are
valid saved entries; the experiment alone proves no general equivalence or
speed improvement. Test reference-shape reuse on the same six-job pilot
before expanding it throughout the finite batch.

At the milestone90 snapshot, the existing geometric process has successful
receipts for classes 0 through 12; its full 127-class batch remains active.
The case7302 replay has 449 distinct successful modules
(455 raw successful rows). Its local-share theorem and
final audit remain pending. Both live processes must be inspected before
any restart. The checkpoint contains immutable observations and a delta log
archive. The upper-bound and reference-premise limitations remain unchanged.

Milestone 91 completes the reference-pattern reuse experiment. Three generic
Lean audits certify bounded cache lookup with complete descriptor equality;
five concrete audits check 156 patterns, two count lists, all six assignments
and the same membership conclusion as the direct pilot. The original 3,732
reference entries and 108 nonreference entries remain covered. The two direct
theorems are rechecked for timing and are not new results.

Direct proof trials took 18.812 and 37.875 seconds; cached trials took 24.203
and 28.016 seconds. Cached timings include descriptor correspondence and
assembly. Additional generic and data setup took 46.125 and 45.219 seconds.
Two other Lean processes were active throughout; the small concurrent sample
does not establish a speed advantage. The selected method for the full witness
batch is the direct balanced-lookup checker. Do not repeat the cache benchmark
without a materially changed representation or a new reason.

The milestone91 snapshot records geometric classes 0 through 19 and 493
distinct successful case7302 modules. Both existing processes continue; the
full geometry batch and local-share theorem remain pending. Use the newer
snapshot and actual process state when continuing. The complete context
assignment, full-key membership and endpoint identities remain open.

The remaining structural work is to supply the two closed reference
catalogue proofs and a concrete Lean retention cover with endpoint-column
identities. The universal conditional indexing argument is now supplied.
Every three-ID credit needs every compatible eleven-direction interpretation;
forgotten coordinate returns can produce several variants. Alternative lower
bounds on the same five shares combine by maximum. Complete the finite
potential replay and the five remaining target share theorems before removing the 234
qualification.

An executable audit checks the exact Python selector assignments on all 37,875
history/direction pairs and agrees with the strict scan proved in Lean. It is
separate from the Lean theorem; the Python interpreter is not encoded there.
Neither check proves retained-edge membership or credit validity.

## Results that constrain further optimisation

Milestone 74 gives exact short-walk obstructions for six specified weakenings
of the target share rules. Under the current boundary budget, a different
constant slope or potential on each entire weakened graph cannot exclude 235.
These are graph obstructions; actual snake realizability was not established.

Productive alternatives therefore require additional information: exclude a
walk through a new geometric fact, restrict to reachable or realizable states,
or improve the boundary contribution with state-dependent endpoint information.
These remain research directions, with no promised numerical improvement.

Milestone 82 supplies another exact obstruction on the completed-share graph.
A four-edge cycle of mean 483 has every count symbol below six. Nonnegative
bonuses that vanish on such edges preserve this mean. Even range zero cannot
meet the current 234 criterion: 227*483 falls short of 111960 by 2319. Six
Lean audits check the arithmetic, separately from the exact array checks.
This does not establish that the graph cycle occurs in an actual snake.

On this witness, the pending 012034 floor 20 occurs twice and 012340 floor 16
once. Assuming both increases its mean to 497. This concerns one cycle only;
the full graph mean and the other pending targets remain unresolved. These
two targets are useful next tests within empty-square charging.

## Preservation and environment

Use the repository sources and milestone receipts as the reproducible record.
The dated handover contains detailed environment paths and earlier evidence.
Milestone 77 saves its coverage checks, superseded memory-intensive attempts
and replay snapshot. Milestone 78 saves the selector/state checks. Milestone 79 saves the encoded
guards, interval-filter assembly, catalogue audit and a later replay observation.
Milestone 81 saves the forty-rule theorem, independent review and exact comparison.
Milestone 84 saves the three-history theorem. Milestone 85 saves the exact reference
table, conditional theorem, provenance review, exhaustive comparison and a later
case7302 observation. Milestone 86 incorporates these results into the paper; its manifest identifies that revision. Milestone 92 contains the current shared handover versions and later proof-process observations.
Build objects remain local and are excluded from Git. Reproduction
uses Lean 4.19.0 with hash-checked inherited support; it does not rebuild the
whole inherited dependency closure.

The smaller coverage implementation splits at six directions, then splits the
largest branch once more. All twelve branches, its seven subcases, rejected
prefixes and their assembly require Lean proofs. The
generation script itself is outside the trusted proof argument. Preserve the
completed case7305 receipts; inspect actual processes before starting any
new case. Do not repeat its successful unchanged replay. Tool session numbers are local to the original execution context.

Milestone 88 freezes 348 successful case7302 replay rows, including 84 newly observed since milestone 87. The log archive and hash scopes are explicit. This is a partial snapshot; the final local-share theorem remains pending.

Milestone 89 freezes 389 distinct successful replay modules, including 41 newly observed since milestone 88. The raw record contains 395 successful rows because the inherited driver repeats composition rows when resumed. Duplicate rows are not counted as new modules.
