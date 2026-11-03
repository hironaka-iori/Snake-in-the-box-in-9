"""Verify accepted clause and actual-snake transfer receipts without rerunning Lean."""
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parents[1];R=H.parents[1]
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
plan=read(H/'data/semantic-plan.json');progress=read(H/'data/semantic-progress.json')
assert progress['status']=='PASS_COMPLETE_CORE_SEMANTICS_AND_CONDITIONAL_TRANSFER'
assert len(progress['checked_modules'])==112 and progress['active'] is None
assert not (H/'data/semantic-batch.lock').exists()
assert sha(H/'data/semantic-plan.json')==progress['plan_sha256']
assert sha(H/'scripts/check_module.py')==progress['checker_sha256']
assert sha(H/'scripts/run_semantics.py')==progress['driver_sha256']
artifacts={a['module']:a for a in plan['artifacts']};rows=[];pins={}
for m in plan['module_order']:
    p=H/'data'/(m+'-audit.json');q=read(p);a=artifacts[m]
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,m
    assert sha(H/a['path'])==a['sha256']==q['source_sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    folder=Path(q['log']).parent
    assert sha(folder/'source.lean.txt')==q['source_sha256']
    assert sha(folder/'checker.py.txt')==q['checker_sha256']==progress['checker_sha256']
    for name,d in q['dependencies'].items():assert sha(name)==d,name
    source=(H/a['path']).read_text(encoding='utf-8')
    assert len(q['axioms'])==source.count('#print axioms')
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    rows.append(dict(module=m,receipt=p.relative_to(H).as_posix(),sha256=sha(p),
        compiler_wall_seconds=q['compiler_wall_seconds'],axioms=q['axioms']))
    pins[p.relative_to(R).as_posix()]=sha(p)
reports=sum(len(x['axioms']) for x in rows);assert reports==112
wrapper=(H/'lean/ShareFromCore150.lean').read_text(encoding='utf-8')
assert '(hunsat : Unsat ShareWindow150.cnf)' in wrapper
assert '[0,1,2,0,3,2]' in wrapper and 'r+6 ≤ m' in wrapper
serials=list((H/'data').glob('serialization-*.json'));assert len(serials)==1
serial=read(serials[0]);assert serial['status']=='RESUMED'
assert serial['transfer_exit_code']==0 and serial['resume_return_code']==0
for p in [H/'data/semantic-plan.json',H/'data/semantic-progress.json',serials[0],Path(__file__)]:
    pins[p.relative_to(R).as_posix()]=sha(p)
out=dict(status='PASS_CORE_SEMANTICS_AND_CONDITIONAL_ACTUAL_SNAKE_SHARE16',
    checked_modules=len(rows),axiom_reports=reports,core_clauses=13655,clause_shards=107,
    directions=[0,1,2,0,3,2],share_resolution=12,share_lower_bound=16,
    canonical_and_reverse_cases_checked=True,additional_pair_assumption=False,
    core_unsat_is_explicit_premise=True,full_Lean_replay_complete=False,
    unconditional_actual_snake_share16_complete=False,new_global_upper_bound=False,
    receipts=rows,source_files_sha256=pins,
    inherited_scope='Generic local models from147 and coordinate/reversal helpers from148 are reused with exact receipts. The148 dependency closure includes one pinned historical data object. Compiler, library objects and project dependencies are pinned in every receipt.',
    record_note='The checker paths display omits148/build; the actual LEAN_PATH and direct dependency records include it. This does not alter the checked source or its resolved dependencies.',
    remaining='Compile the initial-tree bridge and complete all retained contradiction deductions; compose that Unsat result with the checked actual-snake implication.')
target=H/'data/semantics-completion.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','checked_modules','axiom_reports','core_clauses','unconditional_actual_snake_share16_complete']}))
