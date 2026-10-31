"""Negative scope mutations must fail before any specialized score22 claim."""
from pathlib import Path
import copy,gzip,json,subprocess,sys
R=Path(__file__).resolve().parent;S=R/'scope_negative_controls';S.mkdir(exist_ok=True)
with gzip.open(R/'loop_k1_cap21_r4_all8/checked_unsat.json.gz','rt',encoding='utf-8') as f:payload=json.load(f)
with gzip.open(R/'probes/k1_cap0.json.gz','rt',encoding='utf-8') as f:valid_cap0=json.load(f)
valid_cap0['static_cycles']=[];valid_cap0['meta']['geometry_radius']=4
manifest=json.loads((R/'certificate/manifest.json').read_text());rows=[]
mutations=[('cap0','cap_scaled21','cap_excluded',0),('multiple_centres','path','window',[0,1,3,7,6]),('bonus_false','bonus','occupancy_bonus',False),('wrong_objective','objective','objective','21alpha'),('radius3','geometry_radius','geometry_radius',3)]
for name,meta_key,manifest_key,value in mutations:
 d=valid_cap0 if name=='cap0' else {'meta':dict(payload['meta'])}
 d['meta'][meta_key]=value;inp=S/(name+'.json.gz')
 with gzip.open(inp,'wt',encoding='utf-8',compresslevel=1) as f:json.dump(d,f)
 p=subprocess.run([sys.executable,str(R/'export_certificate.py'),'--input',str(inp),'--out',str(S/'unused_output')],capture_output=True,text=True)
 assert p.returncode!=0 and 'score22 exporter requires' in p.stderr,(name,p.stdout,p.stderr)
 folder=S/('verify_'+name);folder.mkdir(exist_ok=True);m=dict(manifest);m[manifest_key]=value;(folder/'manifest.json').write_text(json.dumps(m))
 q=subprocess.run([sys.executable,str(R/'verify_certificate.py'),str(folder),'--rebuild'],capture_output=True,text=True)
 assert q.returncode!=0 and 'manifest does not support' in q.stderr,(name,q.stdout,q.stderr)
 rows.append({'mutation':name,'export_rejected_by_scope_guard':True,'verification_rejected_by_scope_guard':True})
result={'negative_scope_controls':rows,'cap0_input_contains_actual_valid_cap0_UNSAT_proof':True,'specialized_score22_capsule_not_applicable_to_other_queries':True}
(R/'certificate_scope_results.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
