"""Audit the bounded15-bit replay and full initial-tree connection."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parents[1];H=P/'replay';R=P.parents[1]
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
assert len(plan['module_order'])==len(progress['checked_modules'])==36
assert not (H/'data/replay-batch.lock').exists()
artifacts={x['module']:x for x in plan['artifacts']};rows=[]
for m in plan['module_order']:
    p=H/'data'/(m+'-audit.json');q=read(p)
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,m
    assert sha(q['source'])==q['source_sha256']==artifacts[m]['sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']
    for x,d in q['dependencies'].items():assert sha(x)==d,x
    assert len(q['axioms'])==Path(q['source']).read_text(encoding='utf-8').count('#print axioms')
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    rows.append(dict(module=m,receipt=p.relative_to(H).as_posix(),sha256=sha(p),axioms=q['axioms'],
        compiler_wall_seconds=q['compiler_wall_seconds'],seconds=q['seconds']))
for x,d in plan['copied_source_pins'].items():assert sha(R/x)==d,x
native=read(H/'data/packed-replay.json')
assert native['status']=='PASS_COMPLETE_RENAMED_AND_PACKED_RUP_REPLAY'
assert (native['deductions'],native['hints'],native['final_original_clause_id'],native['final_tree_key'])==(285541,31017505,647093,11657)
assert native['final_empty']
for x in native['artifacts']:assert sha(H/x['path'])==x['sha256']
q=dict(status='PASS_15BIT_CHECKER_INITIAL_TREE_AND_CHECKPOINT_PILOT',checked_modules=36,
    axiom_reports=sum(len(x['axioms']) for x in rows),initial_core_clauses=12977,initial_subtrees=102,
    deductions_checked=1030,references_checked=6004,full_checkpoint_checked=True,
    complete_python_replay_deductions=285541,complete_python_replay_references=31017505,
    full_Lean_replay_complete=False,actual_snake_share16_complete=False,new_global_upper_bound=False,
    receipts=rows,source_files_sha256={str(p.relative_to(R)):sha(p) for p in [Path(__file__),H/'data/pilot-source-plan.json',H/'data/replay-progress.json',H/'data/packed-replay.json',H/'data/preparation-audit.json']},
    scope='The exact original core transfers to the15-bit initial tree and through the first1030 deductions to a complete checkpoint. The full final contradiction is still required.')
p=H/'data/pilot-completion.json';assert not p.exists();p.write_text(json.dumps(q,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:q[k] for k in ['status','checked_modules','axiom_reports','deductions_checked','references_checked','full_Lean_replay_complete']}))
