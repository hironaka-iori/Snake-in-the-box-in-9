"""Record two completed research rounds and the terminal replay resource stop."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/161-share18-full-replay'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ar=H/'data/threshold-completion.json';a=read(ar)
    assert a['status']=='PASS_FIVE_NUMERICAL_LEAN_STATEMENTS'
    receipt=H/'data/Threshold165-audit.json';assert sha(receipt)==a['receipt_sha256']
    gpath=P/'data/progress-completion-round165.json';g=read(gpath)
    assert g['status']=='PASS_BOUNDED_REPLAY_GROUPS'
    terminal=P/g['progress_record'];assert sha(terminal)==g['progress_sha256'];t=read(terminal)
    assert t['status']=='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE' and t['active'] is None and t['new_modules']==0
    assert t['failed_module']=='ReplayData161_0014'
    fail=terminal.with_name(terminal.stem+'-ReplayData161_0014.log');failure=fail.read_text()
    assert 'free_bytes' in failure and '1809182720' in failure and 'AssertionError' in failure
    prior=R/'milestones/163-share18-replay-continuation/data/completion.json';q=read(prior)
    assert q['status']=='PASS_BOUNDED_PREFIX_COMPOSITION'
    pr=prior.with_name('Prefix163-audit.json');pq=read(pr);assert sha(pr)==q['receipt_sha256']
    for field,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(pq[field])==pq[key]
    for path,d in pq['dependencies'].items():assert sha(path)==d,path
    assert q['total_checked_deductions']==g['total_deductions_in_completed_groups']==33111
    assert q['total_checked_references']==g['total_references_in_completed_groups']==2734960
    assert not (P/'data/replay-batch.lock').exists() and not (R/'work/fullgraph-active.lock').exists()
    protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82','paper/snake9_research.tex':'e46822ed639866f4c188328712c0d5212dc84887c26d52d4f491cd356f18afdb'}
    for p,d in protected.items():assert sha(R/p)==d,p
    assert sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))==protected['paper/snake9_research.tex']
    result=dict(status='PASS_NUMERICAL_COMPARISON_REPLAY_RESOURCE_STOP',new_Lean_arithmetic_statements=5,new_replay_modules=0,accepted_replay_modules=g['accepted_modules'],completed_groups=g['completed_groups'],completed_segments=g['completed_group_segments'],total_checked_deductions=33111,total_checked_references=2734960,remaining_deductions=g['remaining_deductions'],remaining_references=g['remaining_references'],failed_module=t['failed_module'],resource_stop='Startup free memory 1809182720 bytes below unchanged 2 GiB gate; no new compiler started.',evidence_sha256={str(p.relative_to(R)):sha(p) for p in [ar,receipt,gpath,terminal,fail,prior,pr]},protected_files_sha256=protected,full_share18_replay_complete=False,actual_share18_theorem_complete=False,new_unconditional_bound=False,pause_requested=True,recorder_sha256=sha(__file__))
    (H/'data/completion.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    header='''# Two-round stopping point: milestones 164 and 165

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

'''
    body=header+'''The arithmetic receipt is data/Threshold165-audit.json. The five checked
statements cover the scaled threshold, its integral consequence, the old
walk deficits, the new 35-edge deficit and exact comparison, and the
conditional 234-edge consequence. These statements do not supply the
missing global rounding-loss premise or prove graph inequalities in Lean.

The new replay audit pins the terminal batch record and rechecks accepted
sources, objects, logs, dependencies and axiom reports. The original-clause
to checkpoint consequence from milestone 163 was revalidated by hashes.
The first new module, ReplayData161_0014, stopped at its startup gate with
1,809,182,720 bytes available. No new Lean compiler started for that module.
Preserve this record; the resource stop is not a mathematical failure.

On resumption, inspect actual processes and current Git status. Continue
the existing 161 driver with its immutable source plan when the resource
gate permits. Audit completed groups before checking a new prefix theorem.
The unused prepare_prefix.py and audit_prefix.py copies are preparation
only: no Prefix165 source or theorem was generated or checked.

The most direct mathematical follow-up to round 164 is to exclude total
rounding loss at most 3 for candidate snakes with at least 235 edges.
Keep the inherited graph-to-snake obligations explicit. After the complete
replay, perform the three transfers listed in milestone 162's
review/remaining-composition.md. Partial replay does not establish the
local share theorem.

The paper and unrelated local edits were hash-checked and preserved.
'''
    (H/'COMPLETION.md').write_text(body,encoding='utf-8')
    (H/'README.md').write_text('# Milestone 165\n\nRead COMPLETION.md and data/completion.json for the checked results, resource stop and restart instructions.\n',encoding='utf-8')
    for rel in ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']:
        p=R/rel;old=p.read_bytes()
        if not old.startswith(header.encode()):p.write_bytes(header.encode()+old)
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
