"""Accept the entire012032 contradiction only after checking all342 receipts."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/151-countfree-replay-pilot'
T=R/'milestones/150-actual-pair-share'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
progress=read(P/'data/full-replay-progress.json')
if progress['status']!='PASS_COMPLETE_FULL_REPLAY_MODULES' or progress['active'] is not None:
    print(json.dumps(dict(status='WAITING_FOR_COMPLETE_REPLAY',replay_status=progress['status'],checked=len(progress['checked_modules']))))
    raise SystemExit(2)
assert not (P/'data/full-replay-batch.lock').exists()
plan=read(P/'data/full-execution-plan.json')
assert len(progress['checked_modules'])==len(plan['module_order'])==342
assert [x['module'] for x in progress['checked_modules']]==plan['module_order']
assert sha(P/'data/full-execution-plan.json')==progress['plan_sha256']
assert sha(P/'scripts/run_full_replay.py')==progress['driver_sha256']
assert sha(P/'scripts/check_full_replay.py')==progress['checker_sha256']
artifacts={x['module']:x for x in plan['artifacts']};receipts=[];reports=0;peak=0
for x in progress['checked_modules']:
    m=x['module'];p=P/'data'/(m+'-audit.json');q=read(p)
    assert sha(p)==x['receipt_sha256'] and q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert sha(q['source'])==q['source_sha256']==artifacts[m]['sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256'] and sha(folder/'checker.py.txt')==q['checker_sha256']
    for f,d in q['dependencies'].items():assert sha(f)==d,f
    source=Path(q['source']).read_text(encoding='utf-8')
    assert len(q['axioms'])==source.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
    reports+=len(q['axioms'])
    for sample in q['resource_samples']:
        for proc in sample['owned_lean_processes']:peak=max(peak,int(proc['PrivatePageCount']))
    receipts.append(dict(module=m,receipt=p.relative_to(R).as_posix(),sha256=sha(p),
        compiler_wall_seconds=q['compiler_wall_seconds'],seconds=q['seconds'],axioms=q['axioms']))
assert reports==1027
final=read(P/'data/ReplayUnsat150-audit.json')
assert final['axioms'][0]['theorem']=='Snake9.ReplayFull150.unsat'
native=read(T/'replay/data/packed-replay.json')
assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
assert (native['deductions'],native['hints'],native['final_original_clause_id'],native['final_tree_key'])==(58182,5350080,205425,12069)
assert native['final_empty']
for x in native['artifacts']:assert sha(T/'replay'/x['path'])==x['sha256']
for x in native['checkpoints']:assert sha(T/'replay'/x['path'])==x['sha256']
oldreview=P/'audit/replay-review.json'
assert sha(oldreview)=='ed6039bfdfca718e46384b58cff5eee6542010c3dbfee53311bef30c54aab601'
for f,d in read(oldreview)['pins'].items():assert sha(R/f)==d,f
snapshot=H/'data/completed-replay-snapshot.json';assert not snapshot.exists()
snapshot.write_bytes((P/'data/full-replay-progress.json').read_bytes())
out=dict(status='PASS_COMPLETE_012032_CORE_CONTRADICTION',checked_modules=342,axiom_reports=reports,
    segments=878,deductions=58182,references=5350080,initial_core_clauses=13655,
    final_original_empty_clause=205425,final_tree_key=12069,exact_core_unsat_complete=True,
    actual_snake_composition_checked=False,new_global_upper_bound=False,receipts=receipts,
    maximum_sampled_private_bytes=peak,full_execution_plan_sha256=sha(P/'data/full-execution-plan.json'),
    final_unsat_receipt_sha256=sha(P/'data/ReplayUnsat150-audit.json'),
    completed_replay_snapshot_sha256=sha(snapshot),auditor_sha256=sha(Path(__file__)),
    scope='The entire exact retained core contradiction is accepted. The already checked conditional geometric implication still needs its final composition check.')
target=H/'data/replay-completion.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='receipts'}))
