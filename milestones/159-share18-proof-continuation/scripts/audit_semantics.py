"""Audit the completed CNF interpretation without rerunning accepted Lean jobs."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
plan=read(H/'data/semantic-execution.json')
final_plan=read(H/'data/semantic-final-execution.json')
assert len(plan['module_order'])==109 and len(plan['new_module_order'])==108
for p,d in plan['input_pins'].items():assert sha(p)==d,p
assert sha(H/'scripts/check_semantic.py')==plan['checker_sha256']
assert sha(H/'scripts/run_semantics.py')==plan['driver_sha256']
for p,d in final_plan['input_pins'].items():assert sha(p)==d,p
assert sha(H/'scripts/check_semantic_final.py')==final_plan['checker_sha256']
assert sha(H/'scripts/run_semantics_final.py')==final_plan['driver_sha256']
reports=[];receipts={};checked_deps={}
for module in plan['module_order']:
    src=H/'lean'/(module.replace('.','/')+'.lean')
    assert sha(src)==plan['source_sha256'][module]
    assert src.read_bytes()==(R/'milestones/144-countfree-share18/lean'/(module.replace('.','/')+'.lean')).read_bytes()
    if module=='LocalWindowCnf.ShareWindow144':continue
    rp=H/'data'/(module+'-audit.json');q=read(rp)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    expected_checker=final_plan['checker_sha256'] if module in final_plan['new_module_order'] else plan['checker_sha256']
    assert q['source_sha256']==sha(src) and q['checker_sha256']==expected_checker
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']
    assert len(q['axioms'])==src.read_text().count('#print axioms')
    for item in q['axioms']:assert set(item['axioms'])<={'propext','Classical.choice','Quot.sound'}
    for p,d in q['dependencies'].items():
        if p in checked_deps:assert checked_deps[p]==d,p
        else:assert sha(p)==d,p;checked_deps[p]=d
    receipts[rp.relative_to(H).as_posix()]=sha(rp);reports.extend(q['axioms'])
assert len(reports)==108
assert sum(x['theorem'].rsplit('.',1)[-1].startswith('shard') for x in reports)==104
assert any(x['theorem']=='Snake9.LocalWindow.ShareWindow144.sat' for x in reports)
progress=read(H/'data/semantic-progress.json')
assert progress['status']=='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE' and len(progress['checked'])==106
assert progress['failed_module']=='Share144.Compose'
final_progress=read(H/'data/semantic-final-progress.json')
assert final_progress['status']=='PASS_COMPLETE_SEMANTIC_MODULES' and final_progress['checked']==['Share144.Compose','Share144.Sat']
assert not (H/'data/semantic-batch.lock').exists()
assert not (H/'data/semantic-final-batch.lock').exists()
old=read(R/'milestones/144-countfree-share18/data/export-review.json')
assert old['core_clauses']==13224 and old['semantic_shards']==104
receipt=dict(status='PASS_COMPLETE_UNIVERSAL012034_CNF_INTERPRETATION',
    modules=109,new_checked_modules=108,reused_CNF_modules=1,semantic_shards=104,
    original_core_clauses=13224,axiom_reports=108,all_original_source_bytes_preserved=True,
    theorem='Snake9.LocalWindow.ShareWindow144.sat',
    theorem_scope='Every pair of Boolean selection/endpoint predicates satisfying AxiomsS for the fixed window, bounds and cap has a satisfying assignment of this CNF.',
    original_cnf_to_initial_tree_bridge_previously_complete=True,
    complete_contradiction_replay=False,actual_snake_share18_theorem=False,new_global_bound=False,
    execution_plan_sha256=sha(H/'data/semantic-execution.json'),final_execution_plan_sha256=sha(H/'data/semantic-final-execution.json'),receipt_sha256=receipts,
    final_axioms=next(x['axioms'] for x in reports if x['theorem']=='Snake9.LocalWindow.ShareWindow144.sat'),
    audit_source_sha256=sha(__file__),next_full_paper_revision=166)
(H/'data/semantics-completion.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(receipt['status'],receipt['modules'],'modules',receipt['axiom_reports'],'axiom reports')
