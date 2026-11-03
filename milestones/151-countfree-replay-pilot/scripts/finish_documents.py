"""Publish readable scope and continuation notes after the bounded replay passes."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
group=read(H/'data/first-group-completion.json');pilot=read(H/'data/pilot-completion.json')
assert group['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
assert read(H/'data/paper-source-review.json')['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
note=r'''# Checked initial state and first replay block for 012032

The exact count-free 012032 core now connects, in Lean, to the materialized
initial proof state and to a verified checkpoint after the first 32 replay
segments. This closes the initial-state requirement left in milestone 150.
It does not yet establish the complete contradiction.

## What is checked

All 38 pilot modules passed, with 120 accepted axiom reports. They connect
all 13,655 retained clauses, partitioned into 107 chunks, to the initial
tree and check the first 2,169 deductions with 6,151 propagation references.
Every assignment satisfying the retained core therefore satisfies the
checkpoint obtained by this prefix.

Eleven further module checks extend the result through the first 32
segments: 3,728 deductions and 195,386 references. The final check in this
block verifies the next stored checkpoint, and the block theorem transfers
truth to it. The two prefix counts overlap; they must not be added.

There are 49 accepted modules out of 342 in the complete generated replay.
The complete source contains all 878 segments, 27 transitions between
stored checkpoints, and the final empty clause. The independent source
audit matches every packed deduction and all saved checkpoints, and verifies
that every group occurs in the final composition. Its source inspection
does not replace checking the remaining proof in Lean.

## Mathematical consequence and limitation

The completed result in milestone 150 says that unsatisfiability of this
exact core implies

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16
\]

for every fitting actual-snake window with canonical directions 012032,
including reversal. There is no additional pair-count, parity or specified
endpoint-position assumption. The present checkpoint checks part of the
contradiction needed by that implication. The remaining 846 segments and
final assembly must pass before the actual-snake share theorem is complete.

No new global upper bound follows. Even a completed local share theorem
would discharge only one premise of the conditional 234 profile. The other
local floors, remaining reference refutations and complete potential
certificate remain separate. The maintained interval 191--235 retains the
contributor independent-rebuild limitation. The value 196 and the optimum
remain unresolved.

## Selected continuation

Prioritize the remaining 012032 replay: the new certificate has 342 modules
and 5,350,080 references in total. The existing 012301 job is preserved and
has resumed. These are measured certificate sizes; no full-run timing
improvement is asserted.

Before a new full run, revalidate the existing process and the exact 151
plans and accepted receipts. Use a guarded controller to hold the existing
147 coordinator between checks, run the 151 full replay, and resume the same
147 process afterward or on controller failure. Do not start a second Lean
compiler directly. The first-group controller is limited to 11 new modules;
it is not the controller for the remaining full replay.

Reuse the 49 accepted objects only after matching source, object, log and
dependency hashes. On another machine, restore the archived sources and
rebuild the required dependencies; the current reuse driver assumes the
saved local objects and runtime paths exist. Do not change a receipt to
represent a rebuild that was not executed.

After all 342 modules pass, audit the final unsatisfiability statement and
compose it with the already checked actual-snake implication. Retain the
other upper-bound premises throughout.

## Files and reproduction

`data/pilot-completion.json` and `data/first-group-completion.json` contain
the accepted results. `data/full-execution-plan.json` gives the dependency
order. `data/first-group-progress-snapshot.json` is immutable; the live
`data/full-replay-progress.json` may change when the work resumes and is
excluded from the publication manifest.

All 342 generated sources are preserved in byte-verified archives and remain
available locally. Restore missing files with `scripts/restore_archives.py`.
The full-source plan retains an older command filename in its metadata;
the correct local generator is `scripts/emit_full.py --full --max-source-mib 256`.
The recorded generator hash and generated proof bytes are correct. The
exact packed input remains in milestone 150 and its verified archives.

The paper is updated in both existing locations without new definitions,
author changes or preamble changes. Source checks pass. The compiler helper
fails before TeX, so no new PDF is verified. Last full revision: 146; next: 156.
'''
(H/'MATHEMATICAL_NOTE.md').write_text(note,encoding='utf-8',newline='\n')
readme='''# Milestone 151: initial state and bounded 012032 replay

Lean checked the exact 13,655-clause initial state and the first 32 replay
segments, covering 3,728 deductions and 195,386 references. There are 49
accepted modules among the 342 complete generated sources. Full replay
and final actual-snake composition remain pending; no new global bound.

Read `MATHEMATICAL_NOTE.md` for the result and selected continuation,
`audit/replay-review.md` for the independent review, and the two completion
records in `data/` for accepted checks. Sources are archived with exact
member hashes; originals remain local. The live full-replay progress file
is deliberately outside the immutable publication manifest.

The next selected task is the remaining 012032 full replay, coordinated
with the existing 012301 job so only one Lean compiler runs. Revalidate
live state and reuse accepted work. Do not rerun the completed pilot or
restart the completed 012310 proof.
'''
(H/'README.md').write_text(readme,encoding='utf-8',newline='\n')
update='''# Research update: milestone 151

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

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
             'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_bytes();assert not old.startswith(update.encode());p.write_bytes(update.encode()+old)
p=R/'handoff/NEXT_AGENT_PROMPT.md';old=p.read_text(encoding='utf-8-sig')
assert old.startswith('# Continue after milestone 150')
intro='''# Continue after milestone 151

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

'''
p.write_text(intro+old,encoding='utf-8',newline='\n')
print('Saved151 conclusion and continuation files.')
