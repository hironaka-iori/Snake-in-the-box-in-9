"""Accept the actual-snake consequence only from its completed saved evidence."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1]; R=H.parents[1]
P=R/'milestones/151-countfree-replay-pilot'; T=R/'milestones/150-actual-pair-share'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p); key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]

final_path=H/'data/ShareComplete152-audit.json'
if not final_path.exists():
    print(json.dumps(dict(status='WAITING_FOR_FINAL_ACTUAL_SNAKE_CHECK')))
    raise SystemExit(2)
full=read(H/'data/replay-completion.json')
assert full['status']=='PASS_COMPLETE_012032_CORE_CONTRADICTION' and full['checked_modules']==342
for row in full['receipts']:assert sha(R/row['receipt'])==row['sha256']
assert sha(P/'data/ReplayUnsat150-audit.json')==full['final_unsat_receipt_sha256']
assert sha(P/'data/full-execution-plan.json')==full['full_execution_plan_sha256']
final=read(final_path)
assert final['status']=='PASS' and final['exit_code']==0 and final['stop_reason'] is None
assert len(final['axioms'])==1 and final['axioms'][0]['theorem']=='Snake9.ShareTransfer152.share16'
assert set(final['axioms'][0]['axioms'])<={'propext','Classical.choice','Quot.sound'}
for path,key in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:
    assert sha(final[path])==final[key]
for p,d in final['dependencies'].items():assert sha(p)==d,p
log=Path(final['log']).parent
assert sha(log/'source.lean.txt')==final['source_sha256']
assert sha(log/'checker.py.txt')==final['checker_sha256']
source=Path(final['source']).read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',source)
plan=read(H/'data/completion-plan.json')
assert final['source_sha256']==plan['artifacts'][0]['sha256']
assert 'share16_of_core_unsat Snake9.ReplayFull150.unsat p r hr hshape' in source
semantics=read(T/'data/semantics-completion.json')
assert semantics['status'].startswith('PASS')
review=H/'audit/completion-source-review.json'
assert sha(review)=='2f5b106b50a811dab02c0df9f72f3c4b4b5c7cd7ac798f3df21155fd174f0c65'
recovery_path=H/'data/reboot-recovery-v2-progress.json'
recovery=read(recovery_path)
assert recovery['status']=='PASS_RECOVERED_ACTUAL_SNAKE_COMPOSITION'
assert recovery['previous_processes_confirmed_absent']
assert recovery['final_receipt_sha256']==sha(final_path)
assert [Path(x['script']).name for x in recovery['stages']]==['run_full_replay.py','audit_full.py','check_complete.py']
for stage in recovery['stages']:
    assert stage['exit_code']==0 and sha(stage['log'])==stage['log_sha256']
for path,digest in recovery['pins'].items():assert sha(path)==digest,path
for row in recovery['historical_records']:assert sha(row['archive'])==row['sha256']
# No held coordinator survived the reboot. A RESUMED receipt would be false.
guards=[recovery_path]
record=dict(status='PASS_UNCONDITIONAL_012032_SHARE16',
    actual_snake_share16_complete=True,full_contradiction_complete=True,
    directions=[0,1,2,0,3,2],reversal_included=True,
    assumptions=['Snake in Q9','r+6 <= m','Forward or reversed canonical directions equal012032'],
    extra_count_parity_endpoint_or_unsat_premise=False,new_global_upper_bound=False,
    full_replay_modules=342,full_replay_axiom_reports=1027,
    final_axioms=final['axioms'],standard_library_and_mathlib_trusted=True,
    inherited_historical_data_object_reused=True,
    source_files_sha256={str(p):sha(p) for p in [Path(__file__),final_path,H/'data/replay-completion.json',
        H/'data/completion-plan.json',T/'data/semantics-completion.json',review,guards[0]]},
    recovered_after_reboot=True,
    scope='The local share16 theorem is complete. Four target shapes, reference refutations and the complete global potential certificate remain separate obligations.')
target=H/'data/actual-snake-completion.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record))
