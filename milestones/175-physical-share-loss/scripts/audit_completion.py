from pathlib import Path
import hashlib,json,datetime
h=Path('milestones/175-physical-share-loss').resolve();r=h.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
accepted=[];allpins={}
for p in sorted((h/'data').glob('*-audit.json')):
 j=json.loads(p.read_text())
 if 'module' not in j:continue
 assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
 for key,dkey in [('source','source_sha256'),('object','olean_sha256'),('log','log_sha256')]:assert sha(j[key])==j[dkey],j[key]
 for x,d in j['dependencies'].items():assert sha(x)==d,x;allpins[x]=d
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
 accepted.append({'module':j['module'],'source_sha256':j['source_sha256'],'olean_sha256':j['olean_sha256'],'axiom_reports':len(j['axioms'])})
assert len(accepted)==10,len(accepted)
protected={'.gitignore':'20d6df071a62fabfd98360ddf985088445fde2dec19ef0281f5ab5c6d2b1941b','milestones/50-three-count-return/excess-screen/data/critical-family.json':'466e23170f15072cae3643971b5d9a62b2227fc9ffb4bca276173dc19892db82'}
for x,d in protected.items():assert sha(r/x)==d,x
j={'status':'PASS_ROUND175_CHECKED_RESULTS','start_utc':'2026-11-05T11:31:10+00:00','audit_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'accepted':accepted,'axiom_reports':sum(x['axiom_reports'] for x in accepted),'verified_dependency_files':len(allpins),'protected_files':protected,'new_unconditional_numerical_length_bound':False,'new_actual_boundary':24,'conditional_234_requires_positive_loss':False,'remaining_premises':['Local share floors','Retained graph exclusions and count conditions','Graph-to-snake interpretation and complete finite certificate'],'next_round':176,'pause_after_round':176}
(h/'data/completion.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print({k:v for k,v in j.items() if k not in ['accepted','protected_files','remaining_premises']})
