"""Audit the exact sum theorem, generic budgets, and separate finite experiments."""
from pathlib import Path
from itertools import combinations
import ast,gzip,hashlib,json,re,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
plan=read(HERE/'data/sum-plan.json')
meta=read(HERE/'data/sum-meta/sum3142.json')
mapping=read(HERE/'data/sum-renumbering.json')
assert sha(HERE/'data/sum-renumbering.json')==plan['renumbering_sha256']
rename={int(k):v for k,v in mapping['old_to_new'].items()}
assert sorted(rename)==sorted(rename.values())==list(range(1,2794))
sys.path.insert(0,str(ROOT/'milestones/10-window-aggregate/scripts'))
from gen_lean_sat import TaggedEncoding
enc=TaggedEncoding(meta['window'],[tuple(b) for b in meta['bounds']],radius=4)
lits=[]
for j in meta['positions']:
    i=j+1;v=enc.window[i];used={v^enc.window[i-1],v^enc.window[i+1]}
    lits += [-enc.var[v^(1<<a)^(1<<b)] for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used]
lits.sort();enc.atmost(lits,18,('unproved_sum',))
assert len(lits)==84 and len(set(lits))==70
def clauses(path):
    return [[int(x) for x in line.split()[:-1]] for line in path.read_text().splitlines() if line and not line.startswith(('c','p'))]
original=HERE/'work/012314-upper2-outer18/full.cnf'
assert sha(original)==mapping['original_cnf_sha256'] and clauses(original)==enc.clauses
cnf=HERE/'work/sum314-refined/sum3142.cnf'
assert sha(cnf)==plan['cnf_sha256']
full=clauses(cnf)
assert full==[[rename[abs(v)]*(1 if v>0 else -1) for v in c] for c in enc.clauses]
source=(HERE/'lean/Refined112/LocalWindowCnf/Sum3142.lean').read_text(encoding='utf-8')
raw=ast.literal_eval(source.split('def raw : List (List Nat) :=',1)[1].split('def cnf',1)[0].strip())
decoded=[[x//2 if x%2==0 else -(x//2) for x in c] for c in raw]
assert decoded==[full[i-1] for i in meta['core_ids']] and len(decoded)==3306==plan['core_clauses']
proof=HERE/'work/sum314-refined/sum3142.lrat'
assert sha(proof)==plan['lrat_sha256']
db=dict(zip(meta['core_ids'],decoded));last=len(full);steps=hints=0
for line in proof.read_text().splitlines():
    row=list(map(int,line.split()));z=row.index(0,1);cid,clause,hs=row[0],row[1:z],row[z+1:-1]
    assert row[-1]==0 and cid>last and all(0<h<cid for h in hs)
    assigned={-x for x in clause};contradiction=any(-x in assigned for x in assigned)
    for h in hs:
        premise=db[h]
        if contradiction or any(x in assigned for x in premise):continue
        remaining={x for x in premise if -x not in assigned};assert len(remaining)<=1
        if not remaining:contradiction=True
        else:assigned.add(next(iter(remaining)))
    assert contradiction;db[cid]=clause;last=cid;steps+=1;hints+=len(hs)
assert db[last]==[] and steps==plan['lemmas']==7020 and hints==plan['hints']==367588
for port in plan['ports']:
    a,b=HERE/port['original'],HERE/port['isolated']
    assert sha(a)==port['source_sha256'] and sha(b)==port['isolated_sha256']
    assert re.sub(r'^import Refined112\.',r'import ',b.read_text(encoding='utf-8'),flags=re.M)==a.read_text(encoding='utf-8')
helpers={'SumBudget112':('build','PASS_SUM_BUDGET_ARITHMETIC'),
    'SumCountSemantics112':('build-sum-semantics','PASS_SUM_COUNT_SEMANTICS'),
    'SumGeometry112':('build-sum-geometry','PASS_SUM_GEOMETRY')}
rows=[];audits=[]
for module in list(helpers)+plan['modules']+['ActualSum112']:
    folder,status=helpers.get(module,('build-isolated','PASS_REFERENCE_RECOVERY_MODULE'))
    rp=HERE/'data'/(module+'-audit.json');r=read(rp)
    assert r['status']==status and r['exit_code']==0 and not r['timeout']
    src=HERE/'lean'/(module.replace('.','/')+'.lean')
    obj=HERE/folder/(module.replace('.','/')+'.olean')
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    for path,digest in r['dependencies'].items():
        dep=Path(path)
        if not dep.is_absolute():dep=ROOT/path
        assert sha(dep)==digest,path
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text(encoding='utf-8'))
    if module in helpers or module=='ActualSum112':
        assert not re.search(r'^(?:private )?(?:noncomputable )?(?:def|structure|inductive) ',src.read_text(encoding='utf-8'),re.M)
    audits+=r['theorem_audits'];rows.append(dict(module=module,receipt=rp.relative_to(ROOT).as_posix(),sha256=sha(rp)))
assert len(rows)==40 and len(audits)==20
experiments=[]
for label in ['outer24-middle24','outer30-middle0','expanded24']:
    p=HERE/'data'/label/'results.json';r=read(p)
    assert sha(HERE/'scripts/evaluate_rules.py')==r['script_sha256']
    for path,digest in r['source_files_sha256'].items():assert sha(ROOT/path)==digest
    for profile in r['profiles']:
        buf=gzip.decompress((p.parent/profile['potential_file']).read_bytes())
        assert hashlib.sha256(buf).hexdigest()==profile['potential_sha256']
    experiments.append(dict(path=p.relative_to(HERE).as_posix(),sha256=sha(p),edges=r['edges'],
        comparisons=[dict(profile=q['profile'],mean=q['mean'],range=q['range'],integer=q['comparison_integer_bound']) for q in r['profiles']]))
witness=read(HERE/'data/witness-audit.json')
assert witness['status']=='PASS_SIX_LOCAL_WITNESSES' and sha(HERE/'scripts/audit_witnesses.py')==witness['script_sha256']
for row in witness['witnesses']:assert sha(HERE/row['probe'])==row['sha256']
out=dict(status='PASS_ACTUAL_SUM_THEOREM_AND_SHARED_BUDGET',modules=rows,theorem_audits=audits,
    actual_snake_checked=True,directions=[0,1,2,3,1,4],middle_upper=2,outer_lower=19,
    core_clauses=3306,active_variables=1718,independent_rup_steps=7020,independent_rup_hints=367588,
    new_mathematical_definitions=0,remaining_reference_entries=1366,
    shared_budget_lean_checked=True,generic_sum_semantics_lean_checked=True,complete_graph_lean_certificate=False,
    graph_orientation_guards_lean_checked=False,other_sum_hypotheses_lean_checked=False,
    experiments=experiments,witness_audit_sha256=sha(HERE/'data/witness-audit.json'),
    scope='The012314 middle-at-most2 outer-at-least19 inequality is checked for actual snakes without a collective catalogue premise. Shared excess arithmetic and counter semantics are checked. Other sum hypotheses, complete graph certificates and concrete global integration remain pending; no improved numerical snake bound.')
path=HERE/'data/proof-summary.json';assert not path.exists()
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],'modules',len(rows),'axiom reports',len(audits),'RUP steps',steps)
