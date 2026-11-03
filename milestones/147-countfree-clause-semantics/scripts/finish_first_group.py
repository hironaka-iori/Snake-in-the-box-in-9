"""Audit the first32 complete replay segments and save an immutable checkpoint."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parents[1];H=P/'replay'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
plan=read(H/'data/full-execution-plan.json');progress=read(H/'data/full-replay-progress.json')
assert progress['status']=='PASS_BOUNDED_FULL_REPLAY_PREFIX' and progress['active'] is None
assert len(progress['checked_modules'])==47 and not (H/'data/full-replay-batch.lock').exists()
assert [x['module'] for x in progress['checked_modules']]==plan['module_order'][:47]
artifacts={x['module']:x for x in plan['artifacts']};receipts=[];peak=0
for x in progress['checked_modules']:
    m=x['module'];p=H/'data'/(m+'-audit.json');q=read(p)
    assert sha(p)==x['receipt_sha256'] and q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
    assert sha(q['source'])==q['source_sha256']==artifacts[m]['sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256'] and sha(folder/'checker.py.txt')==q['checker_sha256']
    for f,d in q['dependencies'].items():assert sha(f)==d,f
    assert len(q['axioms'])==Path(q['source']).read_text(encoding='utf-8').count('#print axioms')
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
    for sample in q['resource_samples']:
        for proc in sample['owned_lean_processes']:peak=max(peak,int(proc['PrivatePageCount']))
    receipts.append(dict(module=m,receipt=p.relative_to(H).as_posix(),sha256=sha(p),
        compiler_wall_seconds=q['compiler_wall_seconds'],seconds=q['seconds'],axiom_reports=len(q['axioms'])))
native=read(H/'data/packed-replay.json');segments=native['segments'][:32]
assert segments[-1]['after_step']==8653 and sum(x['hints'] for x in segments)==195344
snapshot=H/'data/first-group-progress-snapshot.json';assert not snapshot.exists()
snapshot.write_bytes((H/'data/full-replay-progress.json').read_bytes())
out=dict(status='PASS_FIRST32_REPLAY_SEGMENTS_AND_CHECKPOINT',checked_modules=47,
    new_modules=11,segments=32,deductions_checked=8653,references_checked=195344,
    total_segments=5089,total_modules=1789,checkpoint_transfer_checked=True,
    maximum_sampled_private_bytes=peak,receipts=receipts,
    new_module_compiler_seconds=sum(x['compiler_wall_seconds'] for x in receipts[36:]),
    full_Lean_replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False,
    progress_snapshot_sha256=sha(snapshot),full_execution_plan_sha256=sha(H/'data/full-execution-plan.json'))
dest=H/'data/first-group-completion.json';assert not dest.exists()
dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in out.items() if k!='receipts'}))
