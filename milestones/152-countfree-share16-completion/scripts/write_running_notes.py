"""Describe the frozen running checkpoint without promoting a partial proof."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
q=json.loads((H/'data/checkpoint.json').read_text(encoding='utf-8-sig'))
assert q['status']=='PASS_ACCEPTED_PREFIX_FULL_REPLAY_RUNNING'
n=q['accepted151_modules']; reports=q['accepted_axiom_reports']
note=rf'''# Completion of the 012032 share proof: running checkpoint

The selected task is the complete Lean proof of

\[
\sum_{{j=1}}^5\sigma_{{12}}(x_{{r+j}})\ge16
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

At this checkpoint, {n} of the complete replay's 342 modules are accepted,
with {reports} accepted axiom reports. Their exact sources, compiled objects,
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
{q['active151_controller_pid']} and driver PID {q['active151_driver_pid']},
session {q['active151_session']}. The existing 012301 coordinator PID
{q['held147_pid']}, session {q['held147_session']}, is temporarily held.
It is preserved and is not currently an active compiler. The controller
and watchdog resume the same process after the 012032 batch finishes.

Continuation PID {q['queued_final_pid']}, session {q['queued_final_session']},
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
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
readme=f'''# Milestone 152: complete share-16 proof in progress

The complete 012032 Lean replay is running. This immutable checkpoint
accepts {n}/342 modules and {reports} axiom reports; the full contradiction
and actual-snake composition remain pending. A separately guarded final
audit and composition are already queued. The previous 012301 replay is
held temporarily and will resume with the same coordinator.

The next integer floor, 17, was tested in one bounded query. It timed out
and remains unresolved. All inputs and incomplete output are preserved.

Read `MATHEMATICAL_NOTE.md`, `data/checkpoint.json` and
`audit/completion-source-review.md`. Inspect the live records before acting;
do not duplicate a running job. No new global upper bound is claimed.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
update=f'''# Research update: milestone 152

The 012032 complete Lean replay is running; {n}/342 modules are accepted
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

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_bytes();assert not old.startswith(update.encode());p.write_bytes(update.encode()+old)
p=R/'handoff/NEXT_AGENT_PROMPT.md';old=p.read_bytes()
intro=f'''# Continue after the milestone 152 running checkpoint

Read milestones/152-countfree-share16-completion/MATHEMATICAL_NOTE.md and
data/checkpoint.json. The accepted prefix is {n}/342 modules. Inspect current
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

'''
p.write_bytes(intro.encode()+old)
print(f'RUNNING_CHECKPOINT_DOCUMENTED_{n}_OF_342')
