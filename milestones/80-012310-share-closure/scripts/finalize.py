"""Verify the completed local theorem, combined catalogue and model receipts."""
from pathlib import Path
import datetime,gzip,hashlib,json,subprocess
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/73-countfree-share-catalogue';CASE=OLD/'cases/case7305'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(HERE/'data').mkdir(exist_ok=True)
a=read(CASE/'data/proof-audit.json');assert a['status']=='PASS_LOCAL_SHARE_THEOREM'
assert a['modules']==465 and len(a['theorem_audits'])==100
assert a['directions']==[0,1,2,3,1,0] and a['share_lower']==12
assert any(r['theorem'].endswith('.share_bound') for r in a['theorem_audits'])
assert any(r['theorem'].endswith('.share_bound_rev') for r in a['theorem_audits'])
for name,digest in a['source_sha256'].items():assert sha(CASE/'lean'/(name+'.lean'))==digest
archive=read(CASE/'data/archive.json');assert archive['audit_sha256']==sha(CASE/'data/proof-audit.json')
for r in [archive['lean_archive']]+archive['compact']:assert sha(CASE/r['path'])==r['sha256']
i=read(OLD/'data/integration-audit.json');assert i['status']=='PASS_COMBINED_LOCAL_CATALOGUE_AND_BUDGET'
assert i['case_numbers']==[7300,7304,7305,7306]
assert i['remaining_local_certificate_cases']==[7301,7302,7303,7307,7308]
assert i['remaining_certificate_signature_checked'] and len(i['checks'])==35
assert sha(OLD/'lean/CombinedCatalogue.lean')==i['source_sha256']
assert i['local_audit_sha256'][CASE.relative_to(ROOT).as_posix()]==sha(CASE/'data/proof-audit.json')
model=read(OLD/'data/proved-model.json');previous=read(OLD/'data/assumed-012310x12-model.json')
assert model['status']=='EXACT_PROOF_SUPPORTED_LOCAL_MODEL' and model['additional_share_assumptions']==[]
assert model['mean']=='483' and model['potential_range']==551 and model['edges']==4947008
assert model['all_edge_potential_verified'] and model['conditional_integer_bound']==235
assert model['audited_local_sources'][(CASE/'data/proof-audit.json').relative_to(ROOT).as_posix()]==sha(CASE/'data/proof-audit.json')
for key in ['weight_sha256','potential_sha256','mean','potential_range','cycle']:
    assert model[key]==previous[key],key
raw=gzip.decompress((OLD/'data/proved-potential.i64.gz').read_bytes())
assert hashlib.sha256(raw).hexdigest()==model['potential_sha256']
before=subprocess.check_output(['git','-c','core.commitGraph=false','show','1b8ef3193e4b8572f75bfc280768dbd4b02940b6:milestones/73-countfree-share-catalogue/data/proved-model.json'],cwd=ROOT)
assert json.loads(before)['mean']=='480'
(HERE/'data/previous-proved-model.json').write_bytes(before)
paper=ROOT/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='3c67d4c168ee7fe463f2ea49da3459f2178ee2a655fd45f9ed374f88126f43dd'
command="@(Get-CimInstance Win32_Process | Where-Object { $_.Name -match '^(python|lean|lake)(\\.exe)?$' -and $_.CommandLine -like '*case7305*' } | Select-Object ProcessId,Name,CommandLine) | ConvertTo-Json -Compress"
text=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip()
processes=json.loads(text) if text else [];assert not processes,'A case7305 process is still running'
refs={ref:subprocess.check_output(['git','-c','core.commitGraph=false','rev-parse',ref],cwd=ROOT,text=True).strip()
    for ref in ['HEAD','origin/main','origin/research/unconditional-241']}
paths=[CASE/'data/proof-audit.json',CASE/'data/archive.json',OLD/'data/integration-audit.json',
    OLD/'data/checkpoint.json',OLD/'data/proved-model.json',OLD/'data/proved-potential.i64.gz',
    OLD/'lean/CombinedCatalogue.lean',OLD/'logs/CombinedCatalogue.log']
out=dict(status='PASS_012310_SHARE_CLOSURE_AND_MODEL_COMPARISON',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    git_refs=refs,case_number=7305,case_modules=465,case_theorem_audits=100,combined_theorem_audits=35,
    completed_cases=i['case_numbers'],remaining_local_certificate_cases=i['remaining_local_certificate_cases'],
    unconditional_edge_interval=[191,235],conditional_target=234,model_mean='483',model_potential_range=551,
    model_conditional_fraction=model['conditional_bound'],model_conditional_integer_bound=235,
    prior_assumed_weight_and_potential_exactly_matched=True,case7305_final_theorem=True,observed_case_processes=processes,
    paper_revision=76,paper_sha256=sha(paper),sources={p.relative_to(ROOT).as_posix():sha(p) for p in paths},
    limitations=['Existing inherited support reused; no clean dependency rebuild.',
        'All-edge potential verified by exact Python comparison; complete Lean potential replay remains.',
        'Full arbitrary-snake retained-edge and credit interpretation remain.',
        'No improvement of the unconditional numerical upper bound; exact optimum unresolved.'])
(HERE/'data/checkpoint.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],'100 local audits; 35 combined audits; 5 local targets remain')
