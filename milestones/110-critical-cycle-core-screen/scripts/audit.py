"""Audit exact proof bytes, semantic statements, and separately labelled graph experiments."""
from pathlib import Path
import ast,gzip,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
plan=read(HERE/'data/isolated-plan.json');generation=read(HERE/'data/plain-generation.json')
for p,h in generation['input_files_sha256'].items():assert sha(ROOT/p)==h
for port in plan['ports']:
    a,b=HERE/port['original'],HERE/port['isolated']
    assert sha(a)==port['sha256'] and sha(b)==port['isolated_sha256']
    assert re.sub(r'^import Recovered110\.',r'import ',b.read_text(),flags=re.M)==a.read_text()
name='d012340_a5_5_2_4_5';meta=read(HERE/'data/meta'/(name+'.json'))
full=[[int(x) for x in line.split()[:-1]] for line in (HERE/'work/renumbered'/(name+'.cnf')).read_text().splitlines() if line and not line.startswith(('c','p'))]
source=(HERE/'lean/Recovered110/LocalWindowCnf/D012340A55245.lean').read_text()
raw=ast.literal_eval(source.split('def raw : List (List Nat) :=',1)[1].split('def cnf',1)[0].strip())
decoded=[[x//2 if x%2==0 else -(x//2) for x in c] for c in raw]
assert decoded==[full[i-1] for i in meta['core_ids']] and len(decoded)==1664 and len(full)==59251
assert sha(HERE/'work/renumbered'/(name+'.cnf'))==plan['remapped_cnf_sha256']
proof=HERE/'work/renumbered'/(name+'.lrat');assert sha(proof)==plan['remapped_lrat_sha256']
db=dict(zip(meta['core_ids'],decoded));last=len(full);added=hints=0
for line in proof.read_text().splitlines():
    row=list(map(int,line.split()));z=row.index(0,1);cid=row[0];clause=row[1:z];hs=row[z+1:-1]
    assert row[-1]==0 and cid>last and all(0<h<cid for h in hs)
    assigned={-x for x in clause};contradiction=any(-x in assigned for x in assigned)
    for h in hs:
        premise=db[h]
        if contradiction or any(x in assigned for x in premise):continue
        remaining={x for x in premise if -x not in assigned}
        assert len(remaining)<=1,(cid,h)
        if not remaining:contradiction=True
        else:assigned.add(next(iter(remaining)))
    assert contradiction
    db[cid]=clause;last=cid;added+=1;hints+=len(hs)
assert db[last]==[] and added==2007 and hints==177364
rows=[];audits=[]
for module in plan['modules']+['PlainCount110']:
    rp=HERE/'data'/(module+'-audit.json');r=read(rp)
    assert r['status']=='PASS_REFERENCE_RECOVERY_MODULE' and r['exit_code']==0 and not r['timeout']
    src=HERE/'lean'/(module.replace('.','/')+'.lean');obj=HERE/'build-isolated'/(module.replace('.','/')+'.olean')
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    for p,h in r['dependencies'].items():assert sha(ROOT/p)==h
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    audits+=r['theorem_audits'];rows.append(dict(module=module,receipt=rp.relative_to(ROOT).as_posix(),sha256=sha(rp)))
assert len(rows)==65 and len(audits)==6
assert not re.search(r'^(?:private )?(?:noncomputable )?def ',(HERE/'lean/PlainCount110.lean').read_text(),re.M)
experiments=[]
for folder,script in [('count-profiles-one','evaluate_count_rules.py'),('count-profiles-all','evaluate_count_rules_all.py'),('share-profiles','evaluate_share_rules.py')]:
    path=HERE/'data'/folder/'results.json';r=read(path)
    assert sha(HERE/'scripts'/script)==r['script_sha256']
    for p,h in r['source_files_sha256'].items():assert sha(ROOT/p)==h
    for profile in r['profiles']:
        b=gzip.decompress((path.parent/profile['potential_file']).read_bytes())
        assert hashlib.sha256(b).hexdigest()==profile['potential_sha256']
    experiments.append(dict(path=path.relative_to(HERE).as_posix(),sha256=sha(path),status=r['status'],
        comparisons=[dict(profile=p['profile'],mean=p['mean'],range=p['range'],integer=p['comparison_integer_bound']) for p in r['profiles']]))
one=read(HERE/'data/count-profiles-one/results.json');assert one['additional_removed']==865
out=dict(status='PASS_NEW_LOCAL_COUNT_EXCLUSION',modules=rows,theorem_audits=audits,core_clauses=1664,
    independent_rup_steps=added,independent_rup_hints=hints,directions=[0,1,2,3,4,0],counts=[5,5,2,4,5],
    original_graph_keys=4947008,prior_exclusions=2092,new_exclusions=865,restricted_graph_keys=one['edges'],
    remaining_reference_entries=1366,actual_snake_exclusion_checked=True,new_mathematical_definitions=0,
    finite_experiments=experiments,complete_restricted_graph_lean_certificate=False,
    scope='One new count exclusion checked for actual snakes and both graph orientations. Remaining six native exclusions are unproved. Native finite-graph experiments are separately labelled. No improved numerical snake bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['modules','theorem_audits']},indent=2))
