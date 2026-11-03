# Completion of the 012032 share proof: running checkpoint

The selected task is the complete Lean proof of

\[
\sum_{j=1}^5\sigma_{12}(x_{r+j})\ge16
\]

for every fitting six-transition window of an actual snake in Q9 whose
canonical directions, in either orientation, are 012032. The notation is
the existing five-centre empty-square share; no new definition is introduced.

## What is already established

Milestone 150 checked every retained clause and the implication from the
exact core contradiction to this actual-snake inequality. Its 112 modules
impose no additional pair-count, parity or endpoint-location hypothesis.
The original numerical certificate contains 13,655 core clauses, 58,182
deductions and 5,350,080 propagation references. Its complete packed
transport has 878 segments, and its source inspection passed independently.

At this checkpoint, 154 of the complete replay's 342 modules are accepted,
with 466 accepted axiom reports. Their exact sources, compiled objects,
logs, checker snapshots and dependencies were revalidated. The accepted
prefix extends the earlier 49-module checkpoint. Its progress is preserved
in `data/replay-prefix-snapshot.json`; the live record may already be later.

The full contradiction and final actual-snake composition are still pending
at this checkpoint. Source review of their acceptance conditions found no
blocking defect. The prepared final theorem has only the snake, window-fit
and canonical-shape assumptions once the contradiction is supplied.
The two incomplete-proof guard tests exited without creating acceptance
artifacts. The later controller-snapshot copy initially lacked its parent
directory; the saved snapshot was created after correcting that filesystem
issue. This was not a failed Lean check.

## Stronger bound tested

The next integer target, share at least 17, was tested by adjoining share
at most 16 to the same radius-four necessary conditions, with endpoint
budget two and all five count intervals unrestricted within 0 to 21.
There were no added pair-count hypotheses or extra cycle exclusions.
The input had 11,651 variables and 94,331 clauses.

The solver reached its 60-second limit and was stopped after 62.563 seconds
including monitoring overhead. The result is unresolved. It establishes
neither share at least 17 nor sharpness of 16. The exact input, variable
interpretation, solver output and incomplete proof log are retained in a
byte-verified archive; the incomplete log is not a certificate.

## Current execution and continuation

The existing 012032 replay continues under controller PID
46168 and driver PID 10396,
session 67715. The existing 012301 coordinator PID
15228, session 67526, is temporarily held.
It is preserved and is not currently an active compiler. The controller
and watchdog resume the same process after the 012032 batch finishes.

Continuation PID 50496, session 80927,
is already waiting for that batch. It will audit all 342 receipts and the
complete contradiction, then briefly hold the same 012301 coordinator to
check the final actual-snake theorem. The final watchdog waits for the
owned checker, including its preflight, before allowing the old job to run.
Do not launch another replay or continuation. Revalidate process identities
and the live progress records before any recovery action.

After the final composition passes, run `scripts/audit_actual.py`, then
`scripts/update_paper.py`. The paper update refuses to execute until the
completed actual-snake evidence exists. Check the paper source and use the
built-in compiler on the already open TeX file. Save a separate completion
manifest; leave this running checkpoint immutable. On another machine,
restore archived sources and rebuild required dependencies rather than
reusing receipts as evidence of a compilation that did not occur there.

## Effect on the main problem

Completion would discharge the 012032 share-16 premise of the conditional
234 profile. The other four target shapes, the remaining reference
refutations and the complete potential certificate remain separate.
The maintained interval is 191--235, using the contributor upper theorem
whose complete independent rebuild remains pending. This checkpoint
establishes no new global bound. The optimum and 196 remain unresolved.

Both paper copies remain unchanged during this running checkpoint. Their
authors and preamble are preserved. No PDF rebuild is claimed. The last
full paper revision was 146; the next is due at 156. The research goal
remains active.
