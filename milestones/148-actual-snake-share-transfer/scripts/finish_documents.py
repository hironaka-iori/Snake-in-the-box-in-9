"""Publish the conditional transfer status and preserve the live replay identity."""
from pathlib import Path
import datetime,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1];Q=R/'milestones/147-countfree-clause-semantics'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
write=lambda p,s:p.write_text(s,encoding='utf-8',newline='\n')
t=read(H/'data/transfer-completion.json');assert t['status']=='PASS_CONDITIONAL_ACTUAL_SNAKE_SHARE16_TRANSFER'
paper=read(H/'data/paper-source-review.json');assert paper['status']=='PASS_CONDITIONAL_TRANSFER_PAPER_SOURCE_CHECKS'
summary='''# Research update: milestone 148

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

Read [the checkpoint](milestones/148-actual-snake-share-transfer/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next: 156.
'''
write(H/'README.md',summary.replace('(milestones/148-actual-snake-share-transfer/MATHEMATICAL_NOTE.md)','(MATHEMATICAL_NOTE.md)'))
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 148')
    local=summary.replace('(milestones/148','(../milestones/148') if '/' in name else summary
    write(p,local+'\n## Earlier record\n\n'+old)
write(R/'handoff/NEXT_AGENT_PROMPT.md','''# Continue after milestone 148

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
''')
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
repo=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    head=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    remote_tips=subprocess.check_output(g+['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin'],cwd=R,text=True))
write(H/'data/repository-final-check.json',json.dumps(repo,indent=2)+'\n')
livepath=R/'work/live-replay147.json';live=read(livepath)
live.update(latest_completed_milestone=148,conditional_transfer_receipt=str(H/'data/transfer-completion.json'),
    next_action='Wait for complete replay, audit it, then use148/scripts/check_complete.py ShareComplete148.',
    progress_snapshot=read(Q/'replay/data/full-replay-progress.json'))
write(livepath,json.dumps(live,indent=2)+'\n')
print('PASS_SAVED148_DOCUMENTS')
