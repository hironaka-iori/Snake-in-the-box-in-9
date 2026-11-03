"""Audit complete concrete clause interpretation; retain the Unsat obligation."""
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
plan=read(H/'data/semantic-plan.json');assembly=read(H/'data/assembly-plan.json')
progress=read(H/'data/semantic-progress.json')
assert progress['status']=='PASS_COMPLETE_GENERIC_AND_CONCRETE_CLAUSE_CHECKS'
assert len(progress['checked_modules'])==112 and progress['active'] is None
assert not (H/'data/semantic-batch.lock').exists()
artifacts={x['module']:x for x in plan['artifacts']+assembly['artifacts']}
rows=[];pins={str(Path(__file__).relative_to(R)):sha(__file__)}
for m in plan['module_order']+assembly['module_order']:
    p=H/'data'/(m+'-audit.json');q=read(p);a=artifacts[m]
    assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None,m
    assert sha(H/a['path'])==a['sha256']==q['source_sha256']
    assert sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
    logdir=Path(q['log']).parent
    assert sha(logdir/'source.lean.txt')==q['source_sha256']
    assert sha(logdir/'checker.py.txt')==q['checker_sha256']
    for f,d in q['dependencies'].items():assert sha(f)==d,f
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
    source=(H/a['path']).read_text(encoding='utf-8')
    assert len(q['axioms'])==source.count('#print axioms')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source)
    rows.append(dict(module=m,receipt=p.relative_to(H).as_posix(),sha256=sha(p),
        compiler_wall_seconds=q['compiler_wall_seconds'],seconds=q['seconds'],axioms=q['axioms']))
    pins[p.relative_to(R).as_posix()]=sha(p)
for x in plan['artifacts']:
    if 'source' not in x:continue
    old=R/x['source'];new=H/x['path'];assert sha(old)==x['source_sha256']
    strip=lambda b:b'\n'.join(l for l in b.split(b'\n') if not l.startswith(b'import '))
    assert strip(old.read_bytes())==strip(new.read_bytes())
review=H/'audit/preserved146-review.json'
assert sha(review)=='a9aa416c1867fd9478ed32120042e7d5f964ecb79a0f36b95427fa8cb6da5f8a'
for p in [H/'data/semantic-plan.json',H/'data/assembly-plan.json',H/'data/semantic-progress.json',review]:pins[p.relative_to(R).as_posix()]=sha(p)
reports=sum(len(x['axioms']) for x in rows);assert len(rows)==113 and reports==111
q=dict(status='PASS_COMPLETE_CORE_CLAUSE_INTERPRETATION_AND_ASSEMBLY',checked_modules=len(rows),axiom_reports=reports,
    concrete_clause_modules=102,original_core_clauses=12977,retained_cycle_clauses=6,
    mathematical_input_unchanged=True,all_cycle_clauses_checked=True,
    core_interpretation_complete_under_local_premises=True,
    unsat_implies_local_share16_checked=True,core_unsat_Lean_complete=False,actual_snake_share16_complete=False,
    new_global_upper_bound=False,receipts=rows,source_files_sha256=pins,
    scope='Every assignment satisfying the local path, endpoint and share-cap premises yields a satisfying assignment for the exact retained core. Unsat of that core implies RefutedShare at cap15. The Unsat premise and actual-snake composition remain required.',
    standard_library_scope='Pinned Lean4.19 compiler and direct standard-library imports; standard library trusted. All six project generic sources were freshly compiled.')
p=H/'data/semantics-completion.json';assert not p.exists();p.write_text(json.dumps(q,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:q[k] for k in ['status','checked_modules','axiom_reports','original_core_clauses','retained_cycle_clauses','actual_snake_share16_complete']}))
