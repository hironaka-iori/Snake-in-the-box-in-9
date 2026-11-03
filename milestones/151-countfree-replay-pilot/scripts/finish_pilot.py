"""Audit the complete initial-tree connection and the bounded012032 replay."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/150-actual-pair-share'
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
plan=read(H/'data/pilot-source-plan.json');progress=read(H/'data/replay-progress.json')
assert progress['status']=='PASS_COMPLETE_REPLAY_PILOT' and progress['active'] is None
assert len(plan['module_order'])==len(progress['checked_modules'])==38
assert not (H/'data/replay-batch.lock').exists()
assert sha(H/'data/pilot-source-plan.json')==progress['plan_sha256']
assert sha(H/'scripts/run_replay.py')==progress['driver_sha256']
assert sha(H/'scripts/check_replay.py')==progress['checker_sha256']
artifacts={x['module']:x for x in plan['artifacts']};rows=[];peak=0
for m in plan['module_order']:
    p=H/'data'/(m+'-audit.json');q=read(p)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,m
    assert sha(q['source'])==q['source_sha256']==artifacts[m]['sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']==progress['checker_sha256']
    for x,d in q['dependencies'].items():assert sha(x)==d,x
    source=Path(q['source']).read_text(encoding='utf-8')
    assert len(q['axioms'])==source.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    for sample in q['resource_samples']:
        for proc in sample['owned_lean_processes']:peak=max(peak,int(proc['PrivatePageCount']))
    rows.append(dict(module=m,receipt=p.relative_to(H).as_posix(),sha256=sha(p),axioms=q['axioms'],
        compiler_wall_seconds=q['compiler_wall_seconds'],seconds=q['seconds']))
for x,d in plan['copied_source_pins'].items():assert sha(R/x)==d,x
nativepath=P/'replay/data/packed-replay.json';native=read(nativepath)
assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
assert (native['deductions'],native['hints'],native['final_original_clause_id'],native['final_tree_key'])==(58182,5350080,205425,12069)
assert native['final_empty']
for x in native['artifacts']:assert sha(P/'replay'/x['path'])==x['sha256']
assert native['segments'][0]['after_step']==2169 and native['segments'][0]['hints']==6151
serials=list((H/'data').glob('serialization-*.json'));assert len(serials)==1
serial=read(serials[0]);assert serial['status']=='RESUMED' and serial['resume_return_code']==0 and serial['transfer_exit_code']==0
record=dict(status='PASS_14BIT_INITIAL_TREE_AND_CHECKPOINT_PILOT',checked_modules=38,
    axiom_reports=sum(len(x['axioms']) for x in rows),initial_core_clauses=13655,initial_subtrees=107,
    deductions_checked=2169,references_checked=6151,full_checkpoint_checked=True,
    maximum_sampled_private_bytes=peak,compiler_wall_seconds=sum(x['compiler_wall_seconds'] for x in rows),
    complete_numerical_replay_deductions=58182,complete_numerical_replay_references=5350080,
    full_Lean_replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False,
    receipts=rows,source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),H/'data/pilot-source-plan.json',H/'data/replay-progress.json',nativepath,H/'data/preparation.json',serials[0]]},
    scope='The exact retained core implies truth of the materialized initial tree and of the complete checkpoint after2169 deductions. The final contradiction still requires the rest of the replay.')
target=H/'data/pilot-completion.json';assert not target.exists()
target.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in record.items() if k not in ['receipts','source_files_sha256']}))
