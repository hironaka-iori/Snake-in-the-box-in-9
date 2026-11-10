from pathlib import Path
import json,gzip,hashlib,subprocess
R=Path('E:/Snake-in-a-box');H=R/'milestones/187-clause-interpretation';p=H/'contributors/milestones/31-233-cost/data/keys233_best.json.gz'
j=json.loads(gzip.decompress(p.read_bytes()));paid=[r for r in j['share'] if r[4]!='lean_floor'];assert len(paid)==490
floor_shapes={(0,1,2,0,3,2),(0,1,2,0,3,1),(0,1,2,3,0,4),(0,1,2,3,1,4)}
results={}
for q in [4,5]:
 free=[];critical=[];remaining=[]
 for dirs,counts,level,proved,basis,hints in paid:
  new=max(0,level-q);floor=16 if tuple(dirs) in floor_shapes else 0
  row=dict(directions=dirs,counts=counts,old_level=level,new_level=new,existing_floor=floor,archived_hint_estimate=hints)
  if new<=floor:free.append(row)
  else:
   remaining.append(row)
   if tuple(dirs)==(0,1,2,0,3,4) and new<=15:critical.append(row)
 results[str(q)]=dict(removed_by_existing_floors=len(free),remaining=len(remaining),additional_removed_if_critical_floor15_is_completed=len(critical),remaining_with_critical_floor15=len(remaining)-len(critical),removed_rows=free,critical_rows=critical)
out=dict(source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),original_paid_share_keys=len(paid),plain_keys_unchanged=True,all_233_certificates_still_pending=True,counts_are_native_not_Lean_certified=True,threshold_savings_not_runtime_measurements=True,results=results)
(H/'data/share-slack-census.json').write_text(json.dumps(out,indent=2)+'\n')
(H/'scripts/share_slack_census.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({q:{k:v for k,v in x.items() if not k.endswith('_rows')} for q,x in results.items()},indent=2))
