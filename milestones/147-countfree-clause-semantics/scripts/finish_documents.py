"""Record verified progress and exact remaining obligations."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
write=lambda p,s:p.write_text(s,encoding='utf-8',newline='\n')
assert read(H/'data/semantics-completion.json')['checked_modules']==113
assert read(H/'replay/data/first-group-completion.json')['status']=='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT'
assert read(H/'data/replay-archives.json')['status']=='PASS_BYTE_VERIFIED_REPLAY_ARCHIVES'
paper=read(H/'data/paper-source-review.json')
assert paper['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
summary='''# Research update: milestone 147

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

Read [the checkpoint](milestones/147-countfree-clause-semantics/MATHEMATICAL_NOTE.md).
Last full paper revision: 146. Next full revision: 156.
'''
write(H/'README.md',summary.replace('(milestones/147-countfree-clause-semantics/MATHEMATICAL_NOTE.md)','(MATHEMATICAL_NOTE.md)'))
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md']:
    p=R/name;old=p.read_text(encoding='utf-8');assert not old.startswith('# Research update: milestone 147')
    local=summary.replace('(milestones/147','(../milestones/147') if '/' in name else summary
    write(p,local+'\n## Earlier record\n\n'+old)
write(R/'handoff/NEXT_AGENT_PROMPT.md','''# Continue after milestone 147

Work in E:/Snake-in-a-box. Apply tensai-bishoujo with the user's formal
tone, no emojis and only necessary recurring definitions. Keep the existing
open paper D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex synchronized
with paper/snake9_research.tex. Preserve authors Iori Hironaka, Tommy Ma,
Steven Zhan and the complete preamble. Preserve unrelated .gitignore and
milestone50 critical-family changes. Goal ACTIVE; round147 made progress.
Last full paper revision146; next156. Compilation currently fails before TeX.

Read milestones/147-countfree-clause-semantics/MATHEMATICAL_NOTE.md and
data/checkpoint.json. Semantics113 modules complete,111 axiom reports:
all12977 original core clauses,102 clause modules,six acyclicity cuts.
Semantics147 proves Unsat implies RefutedShare; Unsat is still a premise.
The exact original input is unchanged. Do not repeat those checks.

The replay36-module pilot is complete. The first full32-segment group
also passes:47 accepted modules,8653 deductions,195344 references,complete
checkpoint transfer. The immutable boundary is in
replay/data/first-group-completion.json and first-group-progress-snapshot.json.
The full generated plan has1789 modules,5089segments,160groups and ends in
Unsat of the exact ShareWindow146 core. Every emitted proof literal and
checkpoint was independently compared with the saved packed data.

First inspect replay/data/full-replay-progress.json, its lock, current
processes and any work/live-replay147.json. A remaining full replay may
already be running. Continue the same process, never duplicate it.
If no process is active and the last run ended successfully, resume
scripts/run_full_replay.py; accepted receipts are revalidated and reused.
The script belongs under milestones/147-countfree-clause-semantics.
If a module failed, inspect its exact failure before any new attempt.
Do not mutate source plans, accepted source/object/log/checker snapshots,
or dependency pins. A layout change needs a separate preserved plan.

Lean4.19 rejects its advertised -M option. Use the external memory guard.
Current runners require zero other Lean processes,free>=1.5GiB at launch,
own private memory<=3GiB and free memory>=768MiB. Generic modules use
one thread and8192KiB stack; concrete modules use two threads and65536KiB.
Fullgraph also requires>=3GiBfree and no other fullgraph job.

After complete replay, audit the final Unsat theorem and compose it with
the checked local semantics, coordinate transport and reversal. No actual
share16 theorem exists yet. Keep012032 and012340 as joint dependencies.
The maintained191--235 interval uses the inspected contributor upper proof;
a full independent rebuild is pending. Conditional234 retains its premises.
The196 conjecture and optimum are unresolved. No new global bound in147.

The1397-module012310 count-sum proof is complete and must not be restarted.
The separate012034 share18 proof has a complete initial-tree bridge and
1055-deduction prefix; its remaining full replay is unfinished.

Large immutable replay inputs and all source modules are archived in147.
Use scripts/restore_archives.py to restore missing exact bytes on a fresh
checkout. Objects are local build outputs. See the publication manifest
for exact published files. Live full-replay progress is deliberately
outside the immutable publication boundary. Fetch each round, stage only
manifest files, commit quietly, push and verify remote. Preserve failures.
''')
p=H/'replay/README.md';old=p.read_text(encoding='utf-8')
backup=H/'audit/replay-readme-preparation.txt';assert not backup.exists();backup.write_bytes(p.read_bytes())
current='''# Current replay status after milestone147

All36 pilot modules passed. Full source generation also completed:1789
modules,5089segments,263586537source bytes,within the256MiB generation cap.
The first32segments and checkpoint transfer passed in11additional modules.
The saved boundary is47accepted modules,8653deductions,195344references.
See data/pilot-completion.json and data/first-group-completion.json.
The full contradiction and actual-snake application remain pending.

Resume with ../scripts/run_full_replay.py only after checking live progress
and confirming no existing driver. Plans and accepted source bytes are
immutable. The independent source-layout audit is in
../audit/full-layout-review147.md. Large inputs and sources are available
through ../data/replay-archives.json and ../scripts/restore_archives.py.

## Original preparation record

The following describes the earlier preparation stage. Its unchecked and
deferred statuses are superseded by the accepted receipts stated above.

'''
write(p,current+old)
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
repo=dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    head=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip(),
    remote_tips=subprocess.check_output(g+['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin'],cwd=R,text=True))
write(H/'data/repository-final-check.json',json.dumps(repo,indent=2)+'\n')
print('PASS_SAVED_CURRENT147_DOCUMENTS')
