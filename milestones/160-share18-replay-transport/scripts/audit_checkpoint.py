"""Verify native prefix transport and the three accepted checkpoint modules."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
run=H/'data/prefix1055';native=read(run/'prefix-transport.json');state=read(run/'run-status.json')
assert native['status']==state['status']=='PASS_EXACT_ACCEPTED_PREFIX_TRANSPORT_CHECKPOINT_SOURCE_ONLY'
assert state['exit_code']==0 and state['stop_reason'] is None
assert state['receipt_sha256']==sha(run/'prefix-transport.json')
assert native['prefix_deductions']==native['packed_rows_equal']==1055 and native['prefix_references']==6006
assert native['live_checkpoint_entries_match_prefix_database'] and native['dead_entries_replaced_by_tautologies']
assert not native['Lean_checkpoint_checked']
assert sha(run/native['checkpoint_file'])==native['checkpoint_sha256']
plan=read(H/'data/checkpoint-execution.json')
for p,d in plan['input_pins'].items():assert sha(p)==d,p
assert sha(H/'scripts/check_checkpoint.py')==plan['checker_sha256']
assert sha(H/'scripts/run_checkpoint.py')==plan['driver_sha256']
receipts={};reports=[];seen={}
for m in plan['module_order']:
    src=H/'lean'/(m+'.lean');assert sha(src)==plan['source_sha256'][m]
    qpath=H/'data'/(m+'-audit.json');q=read(qpath)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert q['source_sha256']==sha(src) and q['checker_sha256']==plan['checker_sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']
    assert len(q['axioms'])==src.read_text().count('#print axioms')
    for a in q['axioms']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p,d in q['dependencies'].items():
        if p in seen:assert seen[p]==d,p
        else:assert sha(p)==d,p;seen[p]=d
    receipts[qpath.relative_to(H).as_posix()]=sha(qpath);reports.extend(q['axioms'])
assert len(reports)==2 and any(x['theorem']=='Snake9.Checkpoint160.afterPrefix_true' for x in reports)
progress=read(H/'data/checkpoint-progress.json');assert progress['status']=='PASS_COMPLETE_CHECKPOINT_MODULES' and len(progress['checked'])==3
assert not (H/'data/checkpoint-batch.lock').exists() and not (H/'data/prefix-transport.lock').exists()
sem=R/'milestones/159-share18-proof-continuation/data/semantics-completion.json'
assert read(sem)['status']=='PASS_COMPLETE_UNIVERSAL012034_CNF_INTERPRETATION'
out=dict(status='PASS_ACCEPTED_PREFIX_CHECKPOINT_TRUTH',
    native_receipt_sha256=sha(run/'prefix-transport.json'),source_plan_sha256=sha(H/'data/source-plan.json'),
    execution_plan_sha256=sha(H/'data/checkpoint-execution.json'),receipt_sha256=receipts,
    checkpoint_modules=3,axiom_reports=2,prefix_deductions=1055,prefix_references=6006,
    additional_replay_deductions_checked=0,remaining_replay_deductions=144160,remaining_replay_references=14704875,
    checkpoint_relation='Live entries agree; dead entries become tautologies. The checked cpOk relation preserves TreeTrue.',
    original_CNF_implies_checkpoint_truth=True,full_share18_replay_complete=False,
    actual_share18_theorem_complete=False,new_global_bound=False,
    semantics159_receipt_sha256=sha(sem),audit_source_sha256=sha(__file__),next_full_paper_revision=166)
(H/'data/completion.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],out['checkpoint_modules'],'modules; full replay remains pending')
