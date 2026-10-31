from pathlib import Path
import json,re,hashlib
D=Path('work/branch241-lean')
CASES=[('algebra_remote.json','checked/ScoreAlgebra.lean',9),('charges_remote.json','checked/ScoreCharges.lean',7),('negative_controls_remote.json','checked/NegativeControlsStandalone.lean',11),('lrat_smoke_remote_v1.json','PeerLratSmokeStandalone.lean',2),('finite_geometry_remote.json','checked/FiniteGeometry.lean',5),('lrat_controls_remote.json','PeerLratFormatControlsStandalone.lean',12),('lrat_infrastructure_remote.json','PeerLratInfrastructureStandalone.lean',10)]
results=[]
for log,src,count in CASES:
 d=json.loads((D/log).read_text(encoding='utf-8'));text=(D/src).read_bytes().decode('utf-8-sig');assert hashlib.sha256(text.encode()).hexdigest()==d['source_sha256']
 snapshots=[x['params']['diagnostics'] for x in d['messages'] if x.get('method')=='textDocument/publishDiagnostics' and any(y['message']=='Nat : Type' for y in x['params'].get('diagnostics',[]))]
 assert d['reason']=='end-sentinel-diagnostic-received' and snapshots
 ds=snapshots[-1];assert not any(x.get('severity') in [1,2] for x in ds)
 assert any(x['message']=='"4.19.0"' for x in ds)
 audits=[x['message'] for x in ds if 'axioms' in x['message']];assert len(audits)==count,(log,len(audits),count)
 for a in audits:
  assert 'sorryAx' not in a
  if 'depends on axioms:' in a:assert set(re.search(r'\[(.*?)\]',a).group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'}
 results.append({'source':src,'source_sha256':d['source_sha256'],'log':log,'status':'PASS on official remote Lean 4.19.0','audits':audits,'errors':0,'warnings':0,'seconds':d['seconds']})
for filename,source in [('false_remote.json','checked/DeliberatelyFalse.lean'),('lrat_invalid_remote.json','PeerLratDeliberatelyInvalidStandalone.lean')]:
 f=json.loads((D/filename).read_text(encoding='utf-8'));assert hashlib.sha256((D/source).read_bytes().decode('utf-8-sig').encode()).hexdigest()==f['source_sha256']
 ds=next(x['params']['diagnostics'] for x in reversed(f['messages']) if x.get('method')=='textDocument/publishDiagnostics' and any(y['message']=='Nat : Type' for y in x['params'].get('diagnostics',[])))
 assert any(x['severity']==1 for x in ds) and any('sorryAx' in x['message'] for x in ds)
result={'execution':'Remote official Lean4web, exact lean-v4.19.0; not local binary compilation','local_block':'Windows application control blocked official lean.exe; no bypass attempted','results':results,'false_theorem_negative_control':'correctly rejected with error and sorryAx, never accepted as verified','unique_math_theorems':23,'unique_LRAT_soundness_and_control_theorems':20,'full_certificate_Lean_replay':'NOT DONE','snake_geometry_bridge':'NOT DONE in Lean for new score','new_numeric_bound':'NONE'}
(D/'verification_status.json').write_text(json.dumps(result,indent=2),encoding='utf-8');print(json.dumps({'passed_units':len(results),'unique_math_theorems':23,'LRAT_control_theorems':20,'negative_control':'PASS: false theorem rejected','full_certificate':'UNREPLAYED'},indent=2))

