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
source=(HERE/'lean/LocalWindowCnf/D01234A1542.lean').read_text()
encoded=ast.literal_eval(re.split(r'(?:noncomputable )?def cnf',source.split('def raw : List (List Nat) :=',1)[1],maxsplit=1)[0].strip())
clauses=[[v//2 if v%2==0 else -(v//2) for v in c] for c in encoded]
meta=read(HERE/'upstream/milestones/10-window-aggregate/data/lean_core_direction5/d01234_a1_5_4_2.json')
full=[[int(v) for v in line.split()[:-1]] for line in (HERE/'work/d01234_a1_5_4_2.cnf').read_text().splitlines() if line and not line.startswith(('p','c'))]
assert clauses==[full[i-1] for i in meta['core_ids']]
assert sha(HERE/'work/d01234_a1_5_4_2.cnf')==pins['full_cnf_sha256']
assert sha(HERE/'work/D01234A1542-core.cnf')==pins['core_cnf_sha256']
proof=HERE/'work/d01234_a1_5_4_2.lrat';assert sha(proof)==generation['mapped_lrat_sha256']
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
assert db[last_id]==[] and added==generation['trimmed_lemmas']==270 and hints==1343
plan=read(HERE/'data/isolated-plan.json');rows=[];audits=[]
for port in plan['ports']:
    original=HERE/port['original'];isolated=HERE/port['isolated']
    assert sha(original)==port['source_sha256'] and sha(isolated)==port['isolated_sha256']
    assert re.sub(r'^import Recovered109\.',r'import ',isolated.read_text(),flags=re.M)==original.read_text()
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
assert len(rows)==10 and len(audits)==16
assert {a['theorem'] for a in audits}=={
 *['Snake9.RelaxedGraph109.'+n for n in ['actual_three_counts','actual_forward_retention','actual_reverse_retention',
 'relaxed_01234_refuted','actual_01234_counts','actual_01234_forward','actual_01234_reverse',
 'twelve_reference_entries_refuted','reference_union_iff_remaining_twelve','remaining_twelve_key_count','completed_comparison_barrier','conditional_comparison_barrier']],
 *['Snake9.LocalWindow.D01234A1542.'+n for n in ['check','sat','unsat','ok1']]}
assert pins['entry']['directions']==[0,1,2,3,4] and pins['entry']['symbols']==[1,5,4,2] and pins['entry']['union_index']==1006
for name in ['ActualRelaxed109','NewRelaxed109','ReferenceCoverage109','RangeBarrier109']:
    assert not re.search(r'^(?:private )?(?:noncomputable )?def ',(HERE/'lean'/(name+'.lean')).read_text(),re.M)
native=[]
for filename,script in [('graph-test.json','check_graph.py'),('small-core-screen.json','screen_small_cores.py'),
                       ('candidate-graph-screen.json','screen_candidate_graphs.py'),('restricted-profiles.json','evaluate_restriction.py'),
                       ('obstruction-survival.json','check_obstructions.py')]:
    d=read(HERE/'data'/filename)
    assert sha(HERE/'scripts'/script)==d['script_sha256']
    for p,h in d.get('source_files_sha256',{}).items():assert sha(ROOT/p)==h,p
    native.append(dict(path=filename,status=d['status'],sha256=sha(HERE/'data'/filename)))
screen=read(HERE/'data/small-core-screen.json')
for r in screen['inputs'].values():assert sha(ROOT/r['saved'])==r['sha256']
restriction=read(HERE/'data/restricted-profiles.json')
assert restriction['removed_edges']==2092 and restriction['remaining_edges']==4944916
for row in restriction['profiles']:
    import gzip
    assert hashlib.sha256(gzip.decompress((HERE/'data'/row['potential_file']).read_bytes())).hexdigest()==row['potential_sha256']
assert [(r['mean'],r['range']) for r in restriction['profiles']]==[(483,551),(496,602)]
assert len(read(HERE/'data/obstruction-survival.json')['tests'])==5
out=dict(status='PASS_ACTUAL_SNAKE_EXCLUSION_AND_RESTRICTED_GRAPH_AUDIT',modules=rows,theorem_audits=audits,
    reference_index=1006,root='D01234A1542',directions=[0,1,2,3,4],symbols=[1,5,4,2],
    relaxed_bounds=[[0,1],[0,5],[0,21],[0,2]],recovered_reference_indices=[0,472,495,535,572,602,619,620,1006,1010,1011,1014],
    independent_clause_identity=True,independent_rup_lemmas=added,independent_rup_hints=hints,
    locally_recovered_reference_entries=12,remaining_reference_entries=1366,full_reference_union_checked=False,
    new_mathematical_definitions=0,actual_snake_restriction_checked=True,comparison_range_barriers_checked=True,numerical_graph_audits=native,
    excluded_full_keys=2092,restricted_graph_edges=4944916,complete_restricted_graph_lean_certificate=False,
    input_pins_sha256=sha(HERE/'data/input-pins.json'),generation_sha256=sha(HERE/'data/generation.json'),
    scope='Lean checks the relaxed 01234 exclusion for actual snakes, both graph orientations, and 12 exact reference entries with 1366 remaining. Independent integer graph calculations remove 2092 keys but retain means 483/496, ranges 551/602, and all five floor obstructions. No new numerical bound or clean dependency rebuild.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k not in ['modules','theorem_audits','numerical_graph_audits']},indent=2))
