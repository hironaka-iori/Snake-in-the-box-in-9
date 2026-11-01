"""Summarize only completed audited local cases, preserving unresolved gates."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
portfolio=read(ROOT/'milestones/72-four-count-proof-closure/critical-current/data/portfolio.json')
cases=[]
for index,selected in enumerate(portfolio['selected']):
    out=HERE/'cases'/f'case{7300+index}';audit=out/'data/proof-audit.json'
    row=dict(case_number=7300+index,directions=selected['directions'],required_share=selected['required_share'],status='NATIVE_CERTIFICATE_ONLY')
    if out.exists():row['status']='LEAN_REPLAY_PENDING'
    if audit.exists():
        a=read(audit);assert a['status']=='PASS_LOCAL_SHARE_THEOREM'
        assert a['directions']==row['directions'] and a['share_lower']==row['required_share']
        for module,h in a['source_sha256'].items():assert sha(out/'lean'/(module+'.lean'))==h
        assert any(r['theorem'].endswith('.share_bound_rev') for r in a['theorem_audits'])
        row.update(status='LEAN_CHECKED_WITH_REVERSAL',modules=a['modules'],theorem_audits=len(a['theorem_audits']),proof_audit_sha256=sha(audit))
    cases.append(row)
bridge=HERE/'bridge/data/proof-audit.json';b=read(bridge);assert b['status']=='PASS_CORE_SHARE_BUDGET'
result=dict(status='VERIFIED_PARTIAL_CATALOGUE_GLOBAL_PROBLEM_OPEN',cases=cases,
    completed_cases=[r['case_number'] for r in cases if r['status']=='LEAN_CHECKED_WITH_REVERSAL'],
    bridge_audit_sha256=sha(bridge),bridge_modules=len(b['newly_checked_modules']),bridge_theorem_audits=len(b['theorem_audits']),
    unconditional_edge_interval=[191,235],conditional_target=234,
    finite_model=dict(mean=496,potential_range=600,upper_fraction='137941/587',source_checkpoint='c3bfc952a1a67191391ebc90c681f8fb6e897bb2'),
    remaining=['Complete remaining local share certificates and discharge the partial catalogue premises',
      'Construct arbitrary-snake graph walk with count and history interpretation',
      'Apply each local credit at the exact indices and match boundary accounting',
      'Apply audited finite potential and finish global Lean theorem'],
    scope='Partial Lean catalogue and global share accounting. No new global numerical bound; no fresh rebuild of all inherited dependencies.')
for name in ['coverage','adapter']:
    path=HERE/name/'data/proof-audit.json'
    if path.exists():
        a=read(path);assert a['status'].startswith('PASS_')
        result[name]=dict(status=a['status'],audit_sha256=sha(path),theorem_audits=len(a['theorem_audits']))
path=HERE/'data/integration-audit.json'
if path.exists() and read(path)['case_numbers']==result['completed_cases']:
    a=read(path)
    result['integration']=dict(status=a['status'],audit_sha256=sha(path),remaining_local_certificate_cases=a['remaining_local_certificate_cases'])
result['comparisons']=[]
for path in [HERE/'data/proved-model.json',HERE/'data/assumed-012310x12-model.json']:
    if path.exists():
        a=read(path)
        for rel,h in a['audited_local_sources'].items():assert sha(ROOT/rel)==h
        result['comparisons'].append(dict(path=path.name,status=a['status'],sha256=sha(path),mean=a['mean'],potential_range=a['potential_range'],additional_share_assumptions=a['additional_share_assumptions']))
(HERE/'data').mkdir(exist_ok=True)
(HERE/'data/checkpoint.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],result['completed_cases'],flush=True)
