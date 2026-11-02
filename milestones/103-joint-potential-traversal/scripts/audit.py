"""Audit the joint-traversal proof and matched full-context certificates."""
from pathlib import Path
import hashlib, json, re

HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['sources','receipts','objects']:
    for path,digest in env[group].items():assert sha(ROOT/path)==digest,path
data=read(HERE/'data/candidates.json')
for path,digest in data['inputs_sha256'].items():assert sha(ROOT/path)==digest,path
required=['JointArithmetic103','TreeStep103','JointTraversal103']+[c['module'] for c in data['specs']]
checked=[]; names=set(); definitions=[]
for name in required:
    src=HERE/'lean'/(name+'.lean'); rp=HERE/'data'/(name+'-audit.json'); r=read(rp)
    assert r['status']=='PASS_JOINT_TRAVERSAL_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/(name+'.olean'))==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    source=src.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source)
    definitions+=re.findall(r'^def (\w+)',source,re.M)
    assert len(r['theorem_audits'])==source.count('#print axioms')
    for a in r['theorem_audits']:
        assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
        assert a['theorem'] not in names,a['theorem']; names.add(a['theorem'])
    checked.append(dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
        seconds=r['seconds'],theorem_audits=len(r['theorem_audits'])))
assert sorted(definitions)==['checkJoint','step'],definitions
start=read(HERE/'data/benchmark-start.json')
assert start['other_lean_processes']==[]
assert set(start['order'])=={c['module'] for c in data['specs']}
for name,digest in start['source_sha256'].items():assert sha(HERE/'lean'/(name+'.lean'))==digest
assert start['checker_sha256']==sha(HERE/'scripts/check.py')
comparisons=[]
for profile in ['completed','conditional']:
    for di,q in [(99,37),(0,0)]:
        pair={c['method']:c for c in data['specs'] if (c['profile'],c['direction'],c['history'])==(profile,di,q)}
        assert set(pair)=={'joint','baseline'}
        for k in ['slope','range','cls','root','source_block','target_block','source_node','target_node']:
            assert pair['joint'][k]==pair['baseline'][k],k
        timings={m:next(r['seconds'] for r in checked if r['module']==c['module']) for m,c in pair.items()}
        comparisons.append(dict(profile=profile,direction=di,history=q,
            baseline_seconds=timings['baseline'],joint_seconds=timings['joint'],
            joint_over_baseline=timings['joint']/timings['baseline'],
            modules={m:c['module'] for m,c in pair.items()}))
oldpath=ROOT/'milestones/102-potential-block-reduction/data/proof-summary.json'; old=read(oldpath)
contexts=old['complete_contexts']
for c in data['specs']:
    assert any((x['profile'],x['direction'],x['history'])==(c['profile'],c['direction'],c['history']) for x in contexts)
failed=[]
for p in sorted((HERE/'logs').glob('*-record.json')):
    r=read(p)
    if r['exit_code']==0 and not r['timeout']:continue
    assert sha(HERE/r['log'])==r['log_sha256'] and sha(HERE/r['source_snapshot'])==r['source_sha256']
    failed.append(dict(record=p.relative_to(HERE).as_posix(),sha256=sha(p),module=r['module'],seconds=r['seconds'],timeout=r['timeout']))
out=dict(status='PASS_JOINT_TRAVERSAL_AND_MATCHED_CONTEXT_COMPARISONS',modules=checked,
    theorem_audits=len(names),new_definitions=definitions,complete_contexts=contexts,
    finite_coverage_by_profile=old['finite_coverage_by_profile'],new_profile_contexts=0,
    comparisons=comparisons,preserved_unsuccessful_attempts=failed,
    environment_sha256=sha(HERE/'data/environment.json'),candidates_sha256=sha(HERE/'data/candidates.json'),
    benchmark_start_sha256=sha(HERE/'data/benchmark-start.json'),prior_proof_summary_sha256=sha(oldpath),
    complete_graph_potential_certificates_checked=False,
    timing_scope='One matched sequential pair per profile and context. No other Lean process at launch. End-to-end module time; unrelated system activity is not isolated.',
    scope='A successful joint traversal implies the existing prefix checker. Four profile/context comparisons transfer to the original graph, and add no coverage. No improved global snake bound is proved.')
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checked),'modules;',len(names),'audits')
for row in comparisons:print(row['profile'],row['direction'],row['history'],row['baseline_seconds'],row['joint_seconds'])
