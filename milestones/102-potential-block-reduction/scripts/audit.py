"""Audit bounded block reductions and original-context finite certificates."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['sources','receipts','objects']:
    for path,digest in env[group].items():assert sha(ROOT/path)==digest,path
data=read(HERE/'data/candidates.json')
for path,digest in data['inputs_sha256'].items():assert sha(ROOT/path)==digest,path
required=['PotentialBlocks102','BoundedPrefixTransfer102']+data['root_modules']
required+=[c['module'] for c in data['specs']]+['AllPotentialBlocks102']
required+=['NatBoolean102','ControlledDecide102','ControlledBle102']
checked=[];names=set();sources=[]
for name in required:
    src=HERE/'lean'/f'{name}.lean';rp=HERE/'data'/f'{name}-audit.json';r=read(rp)
    assert r['status']=='PASS_POTENTIAL_BLOCK_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/f'{name}.olean')==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    source=src.read_text(encoding='utf-8');sources.append(source)
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
    assert len(r['theorem_audits'])==source.count('#print axioms')
    for a in r['theorem_audits']:
        assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert a['theorem'] not in names,a['theorem'];names.add(a['theorem'])
    checked.append(dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
        seconds=r['seconds'],theorem_audits=len(r['theorem_audits'])))
assert len(checked)==20 and len(names)==441
combined='\n'.join(sources)
assert not re.search(r'^def ',combined,re.M)
for profile in ['completed','conditional']:
    ids=re.findall(r'\btheorem '+profile+r'_at_(\d+)\b',combined)
    assert len(ids)==206 and set(map(int,ids))==set(range(206))
oldpath=ROOT/'milestones/101-context-specialization/data/proof-summary.json';old=read(oldpath)
classpath=ROOT/'milestones/100-prefix-potential-checker/data/prefix-enumeration-audit.json';classes=read(classpath)['classes']
assert sha(classpath)==read(ROOT/'milestones/100-prefix-potential-checker/data/proof-summary.json')['prefix_enumeration_audit_sha256']
contexts=old['complete_contexts'].copy();comparisons=[]
for c in data['specs']:
    r=next(r for r in checked if r['module']==c['module']);cl=classes[c['cls']]
    assert cl['root']==c['root']
    row=dict(profile=c['profile'],direction=c['direction'],history=c['history'],slope=c['slope'],
        accepted_edges=cl['accepted_codes'],all_codes_covered=46656,module=c['module'],
        seconds=r['seconds'],origin_milestone=102,original_contextCheck_proved=True)
    if c['role']=='benchmark':
        prev=next(x for x in contexts if (x['profile'],x['direction'],x['history'])==(c['profile'],c['direction'],c['history']))
        comparisons.append(dict(**row,archived_seconds=prev['seconds'],archived_module=prev['module'],
            controlled_comparison=False,scope='Same mathematical context, different recorded workloads. No general speedup factor is established.'))
    else:
        assert not any((x['profile'],x['direction'],x['history'])==(c['profile'],c['direction'],c['history']) for x in contexts)
        contexts.append(row)
counts={p:dict(contexts=sum(x['profile']==p for x in contexts),accepted_edges=sum(x['accepted_edges'] for x in contexts if x['profile']==p)) for p in ['completed','conditional']}
assert all(x['contexts']==6 for x in counts.values())
boolean=read(HERE/'data/boolean-comparison-candidates.json')
assert boolean['original_source_sha256']==sha(HERE/'lean/CompletedBlock102D99Q37.lean')
for v in boolean['variants']:assert sha(HERE/'lean'/(v['module']+'.lean'))==v['source_sha256']
start=read(HERE/'data/boolean-comparison-start.json')
assert start['other_lean_processes']==[] and start['sequential_modules']==['NatBoolean102','ControlledDecide102','ControlledBle102']
bd=next(r for r in checked if r['module']=='ControlledDecide102')
bb=next(r for r in checked if r['module']=='ControlledBle102')
boolean_result=dict(profile='completed',context=[99,37],decide_seconds=bd['seconds'],ble_seconds=bb['seconds'],
    ble_over_decide=bb['seconds']/bd['seconds'],start_record_sha256=sha(HERE/'data/boolean-comparison-start.json'),
    outcome='No speedup observed; retain the original decidable leaf comparison' if bb['seconds']>=bd['seconds'] else 'Lower time observed in this single pair; no cross-context performance claim',
    scope='One matched sequential pair with no other Lean process at launch. Same context, weight, roots and acceptance test. Timing does not establish performance on other contexts or isolate unrelated system activity.')
failed=[]
for p in sorted((HERE/'logs').glob('*-record.json')):
    r=read(p)
    if r['exit_code']==0 and not r['timeout']:continue
    assert sha(HERE/r['log'])==r['log_sha256'] and sha(HERE/r['source_snapshot'])==r['source_sha256']
    failed.append(dict(record=p.relative_to(HERE).as_posix(),sha256=sha(p),module=r['module'],seconds=r['seconds'],timeout=r['timeout']))
out=dict(status='PASS_BOUNDED_POTENTIAL_BLOCKS_AND_EIGHT_NEW_CONTEXT_CHECKS',modules=checked,theorem_audits=len(names),
    fixed_block_equations=412,new_definitions=0,complete_contexts=contexts,finite_coverage_by_profile=counts,
    comparisons=comparisons,new_profile_contexts=8,preserved_unsuccessful_attempts=failed,
    boolean_comparison=boolean_result,
    environment_sha256=sha(HERE/'data/environment.json'),candidates_sha256=sha(HERE/'data/candidates.json'),
    prior_proof_summary_sha256=sha(oldpath),prefix_class_audit_sha256=sha(classpath),
    complete_graph_potential_certificates_checked=False,
    scope='Bounded block equalities preserve both potential caps. Eight new complete profile/context checks transfer to the original graph, for six contexts per profile. No improved global snake bound is proved.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checked),'modules;',len(names),'audits;',counts)
