"""Check the recovered clause identity, plain-clause RUP, and closed Lean evidence."""
from pathlib import Path
import ast,hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=read(HERE/'data/input-pins.json');generation=read(HERE/'data/generation.json')
assert not (HERE/'data/check.lock').exists(),'Wait for the existing checker to finish.'
for row in pins['files']:assert sha(ROOT/row['saved'])==row['sha256']
for name,digest in generation['sources'].items():assert sha(HERE/name)==digest,name
source=(HERE/'lean/LocalWindowCnf/Q012A11.lean').read_text()
encoded=ast.literal_eval(source.split('def raw : List (List Nat) :=',1)[1].split('noncomputable def cnf',1)[0].strip())
clauses=[[v//2 if v%2==0 else -(v//2) for v in c] for c in encoded]
meta=read(HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction_r4/d012_a1_1.json')
full=[[int(v) for v in line.split()[:-1]] for line in (HERE/'work/d012_a1_1.cnf').read_text().splitlines() if line and not line.startswith(('p','c'))]
assert clauses==[full[i-1] for i in meta['core_ids']]
assert sha(HERE/'work/d012_a1_1.cnf')==pins['full_cnf_sha256']
assert sha(HERE/'work/Q012A11-core.cnf')==pins['core_cnf_sha256']
proof=HERE/'work/d012_a1_1.lrat';assert sha(proof)==generation['mapped_lrat_sha256']
db=dict(zip(meta['core_ids'],clauses));added=0;hints=0;last_id=len(full)
for line in proof.read_text().splitlines():
    tokens=list(map(int,line.split()));z=tokens.index(0,1)
    cid= tokens[0];clause=tokens[1:z];antecedents=tokens[z+1:-1]
    assert tokens[-1]==0 and cid>last_id and cid not in db and all(0<h<cid for h in antecedents)
    assigned={-x for x in clause};contradiction=any(-x in assigned for x in assigned)
    for h in antecedents:
        assert h in db,('Missing proof input',h)
        if contradiction:continue
        premise=db[h]
        if any(x in assigned for x in premise):continue
        remaining={x for x in premise if -x not in assigned}
        assert len(remaining)<=1,('Non-unit hint',cid,h)
        if not remaining:contradiction=True
        else:assigned.add(next(iter(remaining)))
    assert contradiction,('RUP failed',cid)
    db[cid]=clause;last_id=cid;added+=1;hints+=len(antecedents)
assert db[last_id]==[] and added==generation['trimmed_lemmas']==968 and hints==41184
plan=read(HERE/'data/isolated-plan.json');rows=[];audits=[]
for port in plan['ports']:
    original=HERE/port['original'];isolated=HERE/port['isolated']
    assert sha(original)==port['source_sha256'] and sha(isolated)==port['isolated_sha256']
    assert re.sub(r'^import Recovered107\.',r'import ',isolated.read_text(),flags=re.M)==original.read_text()
for name in plan['modules']:
    rp=HERE/'data'/(name+'-audit.json');r=read(rp)
    assert r['status']=='PASS_REFERENCE_RECOVERY_MODULE' and r['exit_code']==0 and not r['timeout']
    src=HERE/'lean'/(name.replace('.','/')+'.lean');obj=HERE/'build-isolated'/(name.replace('.','/')+'.olean')
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    for a in r['theorem_audits']:
        assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
        audits.append(a)
    rows.append(dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),seconds=r['seconds']))
assert len(rows)==19 and len(audits)==14
assert {a['theorem'] for a in audits}=={
 'Snake9.RecoveredReference107.adjacent_ones_refuted','Snake9.RecoveredReference107.first_reference_key',
 'Snake9.RecoveredReference107.reference_union_iff_remaining','Snake9.RecoveredReference107.remaining_key_count',
 'Snake9.LocalWindow.Q012A11.check','Snake9.LocalWindow.Q012A11.sat','Snake9.LocalWindow.Q012A11.unsat',
 *[f'Snake9.LocalWindow.Q012A11.ok{k}' for k in range(1,8)]}
assert len(pins['entry']['directions'])==3 and pins['entry']['symbols']==[1,1] and pins['entry']['union_index']==0
out=dict(status='PASS_ONE_REFERENCE_REFUTATION_RECOVERED',modules=rows,theorem_audits=audits,
    reference_index=0,root='Q012A11',directions=[0,1,2],symbols=[1,1],
    independent_clause_identity=True,independent_rup_lemmas=added,independent_rup_hints=hints,
    locally_recovered_reference_entries=1,remaining_reference_entries=1377,full_reference_union_checked=False,
    new_mathematical_definitions=0,source_selection_sha256=sha(ROOT/'milestones/105-reference-proof-closure/data/source-selection.json'),
    input_pins_sha256=sha(HERE/'data/input-pins.json'),generation_sha256=sha(HERE/'data/generation.json'),
    scope='One exact reference entry has a regenerated contradiction, checked semantic interpretation, closed Refuted theorem and checked remaining-union equivalence. Standard axioms only. Reuses existing shared objects; no full clean dependency rebuild or new numerical snake bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['modules','theorem_audits']},indent=2))
