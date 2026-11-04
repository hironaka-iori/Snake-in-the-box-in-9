"""Save completion separately from the immutable earlier running checkpoint."""
from pathlib import Path
import datetime,hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
actual=read(H/'data/actual-snake-completion.json')
assert actual['status']=='PASS_UNCONDITIONAL_012032_SHARE16'
assert read(H/'data/reboot-recovery-v2-progress.json')['status']=='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION'
assert read(H/'data/paper-source-review.json')['status']=='PASS_TARGETED_PAPER_SOURCE_CHECKS'
old=read(H/'data/checkpoint.json')
for p,d in old['protected_unrelated_files_sha256'].items():assert sha(R/p)==d,p
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert paper.read_bytes()==editor.read_bytes()
base=subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()
assert base=='d1f8c1c378ae2f559879e809cab959b1690b3723'
note=r'''# Completed universal share bound for 012032

For every fitting six-transition window of a snake in the ninth-dimensional
cube, if its forward or reversed canonical directions are 012032, then

\[
\sum_{j=1}^{5}\sigma_{12}(x_{r+j})\ge16.
\]

The complete contradiction and its application to actual snakes have passed
Lean. There is no extra count, parity, endpoint-location or contradiction
assumption. All 342 replay modules were audited, covering 58,182 deductions,
5,350,080 propagation references and 1,027 axiom reports. The final snake
theorem was checked separately after the full audit. Only the permitted
standard axioms occur in its report; Lean and the external mathematics
libraries remain trusted. The reused coordinate machinery includes one
pinned historically compiled data object.

The computer rebooted after the user pause. Recovery proved the old jobs
absent, preserved their records, revalidated 301 accepted modules and
checked the remaining modules. The original hold records remain historical;
no process-resumption receipt was invented. The first recovery attempt
failed before dispatch because its log directory was absent; the corrected
attempt and both exact sources are preserved.

This completes one local requirement of the conditional upper-bound route.
Four target shapes remain: 012034, 012301, 012340 and 012345. The reference
refutations and complete potential certificate remain separate obligations.
The maintained project interval is 191--235, with the contributor upper
theorem still awaiting a complete independent rebuild. This local theorem
does not establish a new global upper bound or prove the value 196.

The next selected step is the broader critical-context share-17 proof in
milestones 153--155. One contradiction suffices for both exact and weaker
count conditions. The earlier 012301 job retained 448 accepted modules
before the reboot; its old RUNNING record does not indicate a live process.

Read data/actual-snake-completion.json, data/replay-completion.json,
data/completion-checkpoint.json and data/completion-manifest.json.
The earlier data/checkpoint.json remains the original running checkpoint.
'''
(H/'COMPLETION.md').write_text(note,encoding='utf-8',newline='\n')
intro='''# Research update: universal 012032 share 16 completed

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

'''
for name in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md',
             'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
    p=R/name;p.write_bytes(intro.encode('utf-8')+p.read_bytes())
record=dict(status='PASS_COMPLETE_012032_SHARE16_CHECKPOINT',base_commit=base,
    recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    complete_replay_modules=342,complete_replay_axiom_reports=1027,
    actual_snake_theorem_complete=True,new_global_upper_bound=False,goal_status='ACTIVE',
    remaining_local_targets=['012034','012301','012340','012345'],
    maintained_interval=[191,235],full_independent_upper_bound_rebuild_pending=True,
    paper_sha256=sha(paper),paper_source_checks=True,
    pdf_rebuilt=read(H/'data/paper-source-review.json')['pdf_rebuilt'],
    old_running_checkpoint_sha256=sha(H/'data/checkpoint.json'),
    protected_unrelated_files_sha256=old['protected_unrelated_files_sha256'],
    final_receipt_sha256=sha(H/'data/ShareComplete152-audit.json'),
    full_replay_audit_sha256=sha(H/'data/replay-completion.json'),
    actual_snake_audit_sha256=sha(H/'data/actual-snake-completion.json'))
target=H/'data/completion-checkpoint.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
