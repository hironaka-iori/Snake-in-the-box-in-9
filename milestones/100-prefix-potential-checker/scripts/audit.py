"""Audit the complete-context proofs and preserve unsuccessful implementations."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (HERE/'data/check.lock').exists()
env=read(HERE/'data/environment.json')
for group in ['sources','receipts']:
    for path,digest in env[group].items():assert sha(ROOT/path)==digest,path
required=['PrefixChecker100','WeightSpecialization100','ContextEndpoints100','ReducedCompleted100','ReducedConditional100']
checked=[]
for name in required:
    src=HERE/'lean'/f'{name}.lean';rp=HERE/'data'/f'{name}-audit.json';r=read(rp)
    assert r['status']=='PASS_PREFIX_POTENTIAL_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256']==sha(HERE/r['source_snapshot'])
    assert sha(HERE/'build'/f'{name}.olean')==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    assert sha((HERE/r['source_snapshot']).parent/'checker.py.txt')==r['checker_sha256']
    for path,digest in r['dependencies'].items():assert sha(ROOT/path)==digest,path
    assert len(r['theorem_audits'])==src.read_text().count('#print axioms')
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits'])
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
    checked.append(dict(module=name,receipt=rp.relative_to(ROOT).as_posix(),receipt_sha256=sha(rp),
        seconds=r['seconds'],theorem_audits=len(r['theorem_audits'])))
numeric=read(HERE/'data/prefix-enumeration-audit.json')
assert numeric['status']=='PASS_ALL127_PREFIX_ENUMERATIONS'
assert numeric['global_context_weighted_accepted']==4947008
assert numeric['script_sha256']==sha(HERE/'scripts/audit_prefix.py')
for path,digest in numeric['source_files_sha256'].items():assert sha(ROOT/path)==digest,path
specs=read(HERE/'data/contexts.json');contexts=[]
for spec,name in zip(specs,['ReducedCompleted100','ReducedConditional100']):
    row=next(x for x in numeric['selected_contexts'] if (x['direction'],x['history'])==(spec['di'],spec['q']))
    assert row['class_id']==spec['cls'] and row['root']==spec['root']
    proof=next(x for x in checked if x['module']==name)
    contexts.append(dict(profile=spec['profile'],direction=spec['di'],history=spec['q'],slope=spec['P'],
        accepted_edges=row['accepted_codes'],all_codes_covered=46656,root=spec['root'],
        prefix_transitions=row['transitions'],seconds=proof['seconds'],module=name,
        original_contextCheck_proved=True))
old=[]
for name in ['CompletedContext100','ConditionalContext100']:
    src=HERE/'lean'/f'{name}.lean';attempts=sorted((HERE/'logs').glob(f'{name}-*-record.json'))
    row=dict(module=name,source_sha256=sha(src),status='NOT_ATTEMPTED_SUPERSEDED')
    if attempts:
        p=attempts[-1];r=read(p);assert r['source_sha256']==sha(src)
        row.update(status='TIMED_OUT_SUPERSEDED' if r['timeout'] else 'FAILED_SUPERSEDED',
            record=p.relative_to(HERE).as_posix(),record_sha256=sha(p),seconds=r['seconds'])
    old.append(row)
baseline_path=ROOT/'milestones/99-defined-potential-certificates/logs/CompletedContext99-1793642334277275300-record.json'
baseline=read(baseline_path);assert baseline['timeout'] and baseline['seconds']>=300
out=dict(status='PASS_TWO_COMPLETE_DEFINED_GRAPH_CONTEXTS',modules=checked,
    theorem_audits=sum(x['theorem_audits'] for x in checked),contexts=contexts,
    accepted_edges_checked=sum(x['accepted_edges'] for x in contexts),superseded_implementations=old,
    baseline=dict(record=baseline_path.relative_to(ROOT).as_posix(),sha256=sha(baseline_path),
                  timeout=True,seconds=baseline['seconds']),
    prefix_enumeration_audit_sha256=sha(HERE/'data/prefix-enumeration-audit.json'),
    environment_sha256=sha(HERE/'data/environment.json'),
    full_graph_potential_certificates_checked=False,
    scope='Exact full-context potential inequalities for completed35/0 and conditional177/43, with generic prefix soundness and all-code simplification equalities. Only these contexts are certified; all-context and reference/local obligations remain.')
assert out['accepted_edges_checked']==13749
(HERE/'data/proof-summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(checked),'modules;',out['theorem_audits'],'audits;',out['accepted_edges_checked'],'accepted edges')
