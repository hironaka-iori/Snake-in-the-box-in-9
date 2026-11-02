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
source=(HERE/'lean/LocalWindowCnf/D012304A22623.lean').read_text()
encoded=ast.literal_eval(re.split(r'(?:noncomputable )?def cnf',source.split('def raw : List (List Nat) :=',1)[1],maxsplit=1)[0].strip())
clauses=[[v//2 if v%2==0 else -(v//2) for v in c] for c in encoded]
meta=read(HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction5/d012304_a2_2_6-21_2_3.json')
full=[[int(v) for v in line.split()[:-1]] for line in (HERE/'work/d012304_a2_2_6-21_2_3.cnf').read_text().splitlines() if line and not line.startswith(('p','c'))]
assert clauses==[full[i-1] for i in meta['core_ids']]
assert sha(HERE/'work/d012304_a2_2_6-21_2_3.cnf')==pins['full_cnf_sha256']
assert sha(HERE/'work/D012304A22623-core.cnf')==pins['core_cnf_sha256']
proof=HERE/'work/d012304_a2_2_6-21_2_3.lrat';assert sha(proof)==generation['mapped_lrat_sha256']
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
assert db[last_id]==[] and added==generation['trimmed_lemmas']==75 and hints==426
plan=read(HERE/'data/isolated-plan.json');rows=[];audits=[]
for port in plan['ports']:
    original=HERE/port['original'];isolated=HERE/port['isolated']
    assert sha(original)==port['source_sha256'] and sha(isolated)==port['isolated_sha256']
    assert re.sub(r'^import Recovered108\.',r'import ',isolated.read_text(),flags=re.M)==original.read_text()
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
assert len(rows)==9 and len(audits)==15
assert {a['theorem'] for a in audits}=={
 'Snake9.RecoveredReference108.second_reference_refuted','Snake9.RecoveredReference108.second_reference_key',
 'Snake9.RecoveredReference108.allRefutedList_eraseIdx_iff',
 'Snake9.RecoveredReference108.reference_union_iff_remaining_two','Snake9.RecoveredReference108.remaining_two_key_count',
 'Snake9.RecoveredReference108.relaxed_reference_refuted',
 'Snake9.RecoveredReference108.refuted_of_tighter_centres','Snake9.RecoveredReference108.allRefutedList_filter_iff',
 'Snake9.RecoveredReference108.eight_reference_entries_refuted',
 'Snake9.RecoveredReference108.reference_union_iff_remaining_eight','Snake9.RecoveredReference108.remaining_eight_key_count',
 'Snake9.LocalWindow.D012304A22623.check','Snake9.LocalWindow.D012304A22623.sat',
 'Snake9.LocalWindow.D012304A22623.unsat','Snake9.LocalWindow.D012304A22623.ok1'}
assert pins['entry']['directions']==[0,1,2,3,0,4] and pins['entry']['symbols']==[2,2,6,2,3] and pins['entry']['union_index']==472
for name in ['RecoveredReference108','RelaxedReference108','ReferenceCoverage108']:
    assert not re.search(r'^(?:private )?(?:noncomputable )?def ',(HERE/'lean'/(name+'.lean')).read_text(),re.M)
coverage=read(HERE/'data/relaxed-coverage.json')
selection=read(ROOT/'milestones/105-reference-proof-closure/data/source-selection.json')
selected=[x for x in selection['rows'] if x['directions']==[0,1,2,3,0,4] and x['symbols'][0]<=2 and x['symbols'][3]<=2 and x['symbols'][4]<=3]
assert selected==coverage['rows'] and coverage['indices']==[0,472,495,535,572,602,619,620]
out=dict(status='PASS_RELAXED_EXCLUSION_AND_EIGHT_REFERENCE_ENTRIES',modules=rows,theorem_audits=audits,
    reference_index=472,root='D012304A22623',directions=[0,1,2,3,0,4],symbols=[2,2,6,2,3],
    relaxed_bounds=[[0,2],[0,21],[0,21],[0,2],[0,3]],recovered_reference_indices=coverage['indices'],
    independent_clause_identity=True,independent_rup_lemmas=added,independent_rup_hints=hints,
    locally_recovered_reference_entries=8,remaining_reference_entries=1370,full_reference_union_checked=False,
    new_mathematical_definitions=0,source_selection_sha256=sha(ROOT/'milestones/105-reference-proof-closure/data/source-selection.json'),
    input_pins_sha256=sha(HERE/'data/input-pins.json'),generation_sha256=sha(HERE/'data/generation.json'),
    scope='The recovered smaller proof also proves the relaxed bounds [(0,2),(0,21),(0,21),(0,2),(0,3)]. Checked bounds weakening supplies seven exact entries; together with milestone107 there are eight closed entries. Lean proves the full union equivalent to the filtered 1370-entry obligation. Standard axioms only. Existing shared objects reused; no clean dependency rebuild or new numerical bound.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['modules','theorem_audits']},indent=2))
