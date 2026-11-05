# Current continuation after round169

Round169: missing-pair components and a stronger undominated bound

The goal remains active. At an undominated Q9 center, the graph of absent coordinate pairs is either connected or exactly two clique components. Written proof and independent review give e(q)>=8 and L<=95 implies domination. If disconnected, the entire snake alternates between ab crosspairs and ab-1 triples; m=2ab-2 is14,26,34,38. All four cases have saved constructions checked for distinct vertices and every pairwise cube adjacency. Every undominated center of a longer snake has connected missing-pair graph.

Lean verification: seven modules have PASS receipts with 24 printed axiom reports, including the reused six-statement round167 module. New actual-cube pair/triple and endpoint deductions passed; the generic path-closure theorem passed. The finite eight-cycle endpoint inequality also passed. No new axioms, sorry, admit, or native_decide occur in accepted sources. Full component theorem is NOT yet Lean-checked: the actual candidate subset, its closure, outside witnesses, graph classification/counting, and final loss assembly remain.

Resource-safe change: rebuilt only required PathStructure lemmas and replaced finite cube identities with algebraic proofs. The current PathStructure peak sampled180121600 bytes and CubeLocal48136192 bytes. Existing limits unchanged. Historical failed attempts remain in logs and review; current accepted receipts are data/*-audit.json. Undominated167 reuses its original checked object and receipt; all source/object/log/dependency hashes were validated.

No new unconditional numerical upper bound. The conditional234 comparison still needs L>=4 for the relevant dominating snakes and all its other documented local/global premises. Next priority is actual-cube candidate-set closure and component theorem assembly, followed by restrictions on dominating small-loss cases. The six-square result from168 is superseded by the eight-square theorem in the manuscript. Full-paper revision schedule remains next176.

---

Earlier records follow; their pause and weaker-bound statements are historical.

## Resume round 168 first

Goal active. Read milestones/168-undominated-cube-bridge/README.md and review/six-empty-squares.md. New written result e(q)>=6 at an undominated center, loss contribution>=72; full Lean remains pending. Independent review and exhaustive small coordinate-graph checks passed. Current plan has no accepted dependency chain; rebuild EightCycle168, Snake9, PathStructure, CubeLocal, Undominated167, CubeUndominated168 in that order. Preserve resource limits. The prior PathStructure finite irreflexivity test exceeded its limit; it now has an untested algebraic replacement. Do not claim the entire result is Lean-checked. Next complete the graph counting and eight-cycle interpretation. Earlier pause text is historical.

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

# Continue after the milestone 152 running checkpoint

Read milestones/152-countfree-share16-completion/MATHEMATICAL_NOTE.md and
data/checkpoint.json. The accepted prefix is 154/342 modules. Inspect current
progress before acting: the full replay and final-composition continuation
are already running/waiting, and147 is temporarily held. Do not duplicate
them. The source review is complete; proof completion remains pending.

After complete replay and the queued composition succeed, run152
scripts/audit_actual.py, then scripts/update_paper.py; verify and compile the
existing open paper. Publish final evidence in a separate completion
manifest without editing this frozen checkpoint. The complete012310 proof
must not be restarted. The cap16/target17 experiment timed out and should
not be reported as a theorem or a counterexample.

Historical continuation instructions follow; this paragraph takes priority
where their old job status differs. Last full paper revision146; next156.

# Continue after milestone 151

Read milestones/151-countfree-replay-pilot/MATHEMATICAL_NOTE.md and its
checkpoint first. The exact initial-tree bridge and first 32 segments
are accepted: 49/342 modules, 3,728 deductions, 195,386 references.

The selected next task is the remaining 012032 full replay. Its sources,
dependency order and bounded checker are prepared in 151. Do not regenerate
accepted sources or rerun the completed prefix. Reuse its receipts after
checking exact source/object/log/dependency hashes. Full replay is still
uncompleted; after it passes, audit and compose with the checked 150
actual-snake share-16 implication.

The original 147 coordinator (PID 15228, session 67526 at this checkpoint)
has resumed. Verify it live before any action. Prepare a guarded full-run
controller, following the existing suspend/wait/resume and watchdog method,
to run the remaining 151 modules without another active Lean compiler.
The first-group controller has --limit 11 and is already finished; do not
mistake it for the full-run controller. Never restart a confirmed-live job.

The live 151 full-replay progress file is excluded from the publication
manifest; its immutable first-group snapshot is included. Inspect the live
file and process identity before deciding whether a later run has started.
The source plan's old regeneration filename is metadata only; the actual
generator is scripts/emit_full.py. Use the verified archives to restore
missing sources instead of modifying them.

Maintain all remaining local/reference/potential premises of conditional
234. No new global bound follows yet. Preserve unrelated edits and keep
the goal ACTIVE. Earlier notes below record historical choices.

# Continue after milestone 150

Read milestones/150-actual-pair-share/MATHEMATICAL_NOTE.md and
data/checkpoint.json there. The exact 012032 core interpretation and
conditional actual-snake share-16 transfer passed all 112 checks. The
count-free contradiction still needs its Lean replay. Do not treat the
numerical replay or clause semantics as a completed local theorem.

The same 147 full replay for 012301 remains active. Revalidate coordinator
PID 15228 and session 67526 against current process identity and progress.
Do not launch a duplicate. After it completes, audit its exact receipts
and run the guarded 148 final composition. The next new 012032 task is
the prepared 38-module pilot. Serialize compilers; do not generate or
launch its full replay until the initial-tree and prefix pilot passes.

The stronger count-free 012032 proof supersedes the proposed one-unit
actual-pair allowance as the selected task. The weaker cap14 numerical
certificate and allowance note are retained without a second Lean
pipeline. No new global bound follows. Keep all remaining local, reference
and potential premises visible. Preserve unrelated edits and exact bytes.
The goal remains ACTIVE. Earlier continuation notes below are historical.

# Continue after milestone 149

Read milestones/149-share-credit-tradeoff/MATHEMATICAL_NOTE.md first. The
fixed-profile floor15/occurrence-credit tradeoff is ruled out for every
credit. The graph identities and arithmetic have separate evidence; no
new global bound is claimed. Do not repeat this failed tradeoff or run the
unnecessary half-credit experiment. Keep the 012032 floor16 target.

The same147 replay remains the selected next task. Its running coordinator
was resumed after149. Everything below concerning that replay and148's
completed conditional transfer remains applicable. The goal is ACTIVE.

# Continue after milestone 148

Work in E:/Snake-in-a-box. Apply tensai-bishoujo with the user's formal tone,
no emojis and only necessary recurring definitions. Preserve the existing
open paper D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex and its
repository mirror, the three authors and the complete preamble. Leave
unrelated .gitignore and milestone50 critical-family changes untouched.
Goal ACTIVE; 148 made progress. Full paper revision 146; next 156.

First revalidate the existing full 147 replay: unified session 67526,
coordinator PID 15228 at the last check. Inspect current processes and
milestones/147-countfree-clause-semantics/replay/data/full-replay-progress.json.
The lock or an old progress file alone is insufficient. Poll the same
handle; never restart on an observation timeout. work/live-replay147.json
records the last live observation. The driver resumes accepted receipts.

Read milestones/148-actual-snake-share-transfer/MATHEMATICAL_NOTE.md,
data/transfer-completion.json and data/checkpoint.json. The 16 accepted 148
checks contain27 standard-axiom reports. The final two theorems give the
actual five-centre share>=16 for a fitting 012301 shape in either orientation,
from RefutedShare or exact-core Unsat as an explicit argument. There are
no extra count, parity or endpoint-location assumptions.

The generic model and direction/reversal definitions are preserved. One
historical WindowAutomatonData object is reused with source/object/log and
direct dependency hashes plus a fresh axiom audit. Its fresh rebuild hit
the 3 GiB guard. The original Snake9 witness and old DirectionWindowBridge
239 coverage checks also exceeded the guard; transfer-only source copies
retain the unchanged needed proofs and omit those unrelated sections.
All failures and original sources are retained. External Mathlib entry
artifacts are pinned; its full library was not rebuilt.

Final accepted plan: data/transfer-plan-v4.json. Do not rerun v1-v3 or
restart successful148 checks. All serialization controllers resumed the
same 147 coordinator; none remains held. The v4 wrappers are complete only
conditionally. Do not claim the core contradiction or unconditional share 16.

When the 147 driver records PASS_COMPLETE_FULL_REPLAY_MODULES with all 1789
modules and no active process, audit its complete source/object/log/checker
and dependency closure, including the final Unsat theorem. Then run
148/scripts/check_complete.py ShareComplete148. The source is prepared,
but remains uncompiled; its guard refuses to invoke Lean before the full
replay finishes. Inspect its final axiom report and update the actual-snake
status only after successful compilation. Record and investigate any
failure before changing its source or retrying.

Lean 4.19 rejects -M; keep external limits. One compiler at a time, free
memory>=1.5GiB at launch, own private memory<=3GiB, free floor 768 MiB.
148 helpers use one thread and 8192 KiB stack. The 147 full replay uses its
unchanged accepted checker. Do not create a competing compiler process.

Keep 012032 and 012340 as joint dependencies. The maintained 191--235 interval
uses the inspected contributor upper theorem; a complete independent
rebuild remains pending. Conditional 234 retains other local-share,
reference and potential-certificate premises.196 and optimum are unresolved.
The 1397-module 012310 count proof is complete; do not restart it. The
separate 012034 share 18 full replay remains unfinished.

Paper source checks pass. Built-in compilation fails before TeX in the
Windows helper; no rebuilt PDF is verified. Preserve audited bytes, use
manifest-only staging, commit quietly, push and verify remote each round.
