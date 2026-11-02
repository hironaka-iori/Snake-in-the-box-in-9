"""Audit the new interval theorem and separate it from unproved sum experiments."""
from pathlib import Path
import ast,gzip,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
plan=read(HERE/'data/refined-plan.json');meta=read(HERE/'data/refined-meta/middle325r.json')
full=[[int(x) for x in line.split()[:-1]] for line in (HERE/'work/middle-refined/middle325r.cnf').read_text().splitlines() if line and not line.startswith(('c','p'))]
assert sha(HERE/'work/middle-refined/middle325r.cnf')==plan['cnf_sha256']
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding,is_cycle_set
enc=TaggedEncoding(meta['window'],[tuple(b) for b in meta['bounds']],radius=4)
case=read(HERE/'data/probes/middle-3-2-5.json')
for cut in case['cycle_cuts']:
    assert is_cycle_set(cut) and all(v in enc.var for v in cut)
    enc.add([-enc.var[v] for v in cut],('cut',))
assert enc.clauses==full
source=(HERE/'lean/Refined111/LocalWindowCnf/Middle325R.lean').read_text()
raw=ast.literal_eval(source.split('def raw : List (List Nat) :=',1)[1].split('def cnf',1)[0].strip())
decoded=[[x//2 if x%2==0 else -(x//2) for x in c] for c in raw]
assert decoded==[full[i-1] for i in meta['core_ids']] and len(decoded)==plan['core_clauses']==2040
proof=HERE/'work/middle-refined/middle325r.lrat';assert sha(proof)==plan['lrat_sha256']
db=dict(zip(meta['core_ids'],decoded));last=len(full);added=hints=0
for line in proof.read_text().splitlines():
    row=list(map(int,line.split()));z=row.index(0,1);cid=row[0];clause=row[1:z];hs=row[z+1:-1]
    assert row[-1]==0 and cid>last and all(0<h<cid for h in hs)
    assigned={-x for x in clause};contradiction=any(-x in assigned for x in assigned)
    for h in hs:
        premise=db[h]
        if contradiction or any(x in assigned for x in premise):continue
        rest={x for x in premise if -x not in assigned};assert len(rest)<=1
        if not rest:contradiction=True
        else:assigned.add(next(iter(rest)))
    assert contradiction;db[cid]=clause;last=cid;added+=1;hints+=len(hs)
assert db[last]==[] and added==plan['lemmas']==11711 and hints==plan['hints']==611907
for port in plan['ports']:
    a,b=HERE/port['original'],HERE/port['isolated'];assert sha(a)==port['source_sha256'] and sha(b)==port['isolated_sha256']
    assert re.sub(r'^import Refined111\.',r'import ',b.read_text(),flags=re.M)==a.read_text()
rows=[];audits=[]
for module in ['CounterSound111']+plan['modules']+['MiddleCount111']:
    rp=HERE/'data'/(module+'-audit.json');r=read(rp)
    assert r['status']=='PASS_REFERENCE_RECOVERY_MODULE' and r['exit_code']==0 and not r['timeout']
    src=HERE/'lean'/(module.replace('.','/')+'.lean');obj=HERE/'build-isolated'/(module.replace('.','/')+'.olean')
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    for p,h in r['dependencies'].items():assert sha(ROOT/p)==h
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    audits+=r['theorem_audits'];rows.append(dict(module=module,receipt=rp.relative_to(ROOT).as_posix(),sha256=sha(rp)))
assert len(rows)==58 and len(audits)==13
for name in ['CounterSound111','MiddleCount111']:
    assert not re.search(r'^(?:private )?(?:noncomputable )?(?:def|inductive|structure) ',(HERE/'lean'/(name+'.lean')).read_text(),re.M)
experiments=[]
for folder,script in [('middle325-profiles','evaluate_middle.py'),('sum22-profiles','evaluate_outer_sum.py')]:
    p=HERE/'data'/folder/'results.json';r=read(p);assert sha(HERE/'scripts'/script)==r['script_sha256']
    for path,digest in r['source_files_sha256'].items():assert sha(ROOT/path)==digest
    for profile in r['profiles']:
        buf=gzip.decompress((p.parent/profile['potential_file']).read_bytes());assert hashlib.sha256(buf).hexdigest()==profile['potential_sha256']
    experiments.append(dict(path=p.relative_to(HERE).as_posix(),sha256=sha(p),status=r['status'],additional_removed=r['additional_removed'],
        comparisons=[dict(profile=q['profile'],mean=q['mean'],range=q['range'],integer=q['comparison_integer_bound']) for q in r['profiles']]))
out=dict(status='PASS_THREE_COUNT_RESTRICTION',modules=rows,theorem_audits=audits,directions=[0,1,2,3,4,0],
    bounds=case['bounds'],actual_snake_checked=True,independent_rup_steps=added,independent_rup_hints=hints,core_clauses=2040,
    previous_exclusions=2957,new_exclusions=1462,total_exclusions=4419,restricted_graph_keys=4942589,
    remaining_reference_entries=1366,new_mathematical_definitions=0,finite_experiments=experiments,
    outer_sum_inequality_lean_checked=False,complete_restricted_graph_lean_certificate=False,
    scope='A new three-count interval exclusion is checked for actual snakes and both graph orientations. The generalized counter helper is checked separately. Sum inequalities and their bonus integration remain unproved; no improved numerical snake bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['modules','theorem_audits']},indent=2))
