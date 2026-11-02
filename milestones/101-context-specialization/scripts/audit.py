"""Verify exact proof receipts and separate evaluator equations from finite bounds."""
from pathlib import Path
import hashlib, json, re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
assert not (HERE/'data/check-extra.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['sources','receipts','objects']:
    for path,digest in env[group].items():assert sha(ROOT/path)==digest,path
data=read(HERE/'data/generated-contexts.json');finite=read(HERE/'data/finite-contexts.json')
for path,digest in data['inputs_sha256'].items():assert sha(ROOT/path)==digest,path
for path,digest in finite['inputs_sha256'].items():
    p=HERE/'data'/path if path=='generated-contexts.json' else ROOT/path
    assert sha(p)==digest,path
required=['ContextWeights101','DirectionPilot101','ContextPilot101','Direction101Batch02','EmittingPilot101']
required+=data['direction_modules']+data['context_modules']+['AllContextSpecializations101']
required+=['EmittingReduction101']+[c['module'] for c in finite['specs']]
assert len(required)==len(set(required))
checked=[];names=set();source_texts=[]
for name in required:
    src=HERE/'lean'/f'{name}.lean';rp=HERE/'data'/f'{name}-audit.json';r=read(rp)
    assert r['status']=='PASS_CONTEXT_SPECIALIZATION_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/f'{name}.olean')==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    source=src.read_text(encoding='utf-8');source_texts.append(source)
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
    assert len(r['theorem_audits'])==source.count('#print axioms')
    for a in r['theorem_audits']:
        assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert a['theorem'] not in names,a['theorem']
        names.add(a['theorem'])
    checked.append(dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
        seconds=r['seconds'],theorem_audits=len(r['theorem_audits'])))
combined='\n'.join(source_texts)
for prefix in ['direction','conditioned']:
    ids=re.findall(r'\btheorem '+prefix+r'_(\d+)\b',combined)
    assert len(ids)==505 and set(map(int,ids))==set(range(505)),prefix
contexts={(r['direction'],r['history']) for r in data['contexts']};assert len(contexts)==791
for prefix in ['selected','source','target','block','completed','conditional']:
    ids=re.findall(r'\btheorem '+prefix+r'_(\d+)_(\d+)\b',combined)
    assert len(ids)==791 and {tuple(map(int,x)) for x in ids}==contexts,prefix
assert len(names)==5767
old=read(ROOT/'milestones/100-prefix-potential-checker/data/proof-summary.json')
all_contexts=[{**c,'profile':c['profile'].lower(),'origin_milestone':100} for c in old['contexts']]
for c in finite['specs']:
    proof=next(r for r in checked if r['module']==c['module'])
    all_contexts.append(dict(profile=c['profile'],direction=c['direction'],history=c['history'],
        accepted_edges=finite['selection']['accepted_edges'],all_codes_covered=46656,
        slope=c['slope'],module=c['module'],seconds=proof['seconds'],origin_milestone=101,
        original_contextCheck_proved=True))
profile_counts={profile:dict(contexts=sum(c['profile']==profile for c in all_contexts),
    accepted_edges=sum(c['accepted_edges'] for c in all_contexts if c['profile']==profile))
    for profile in ['completed','conditional']}
attempts=[]
for p in sorted((HERE/'logs').glob('*-record.json')):
    r=read(p)
    if r['exit_code']==0 and not r['timeout']:continue
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha(HERE/r['source_snapshot'])==r['source_sha256']
    attempts.append(dict(record=p.relative_to(HERE).as_posix(),sha256=sha(p),
        module=r['module'],exit_code=r['exit_code'],timeout=r['timeout'],seconds=r['seconds']))
out=dict(status='PASS_ALL_CONTEXT_EQUATIONS_AND_TWO_EMITTING_CONTEXT_CHECKS',
    modules=checked,theorem_audits=len(names),direction_equations=505,context_equations=791,
    all_context_weights_and_endpoints_checked=True,complete_contexts=all_contexts,
    finite_coverage_by_profile=profile_counts,new_finite_context=finite['selection'],
    preserved_unsuccessful_attempts=attempts,environment_sha256=sha(HERE/'data/environment.json'),
    generated_contexts_sha256=sha(HERE/'data/generated-contexts.json'),
    finite_contexts_sha256=sha(HERE/'data/finite-contexts.json'),complete_graph_potential_certificates_checked=False,
    scope='All 791 context evaluator equations are checked. Finite potential inequalities are checked for two contexts per profile. No improved global bound follows from this milestone alone.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checked),'modules;',len(names),'theorem audits;',profile_counts)
