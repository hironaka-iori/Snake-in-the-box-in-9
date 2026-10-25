"""Add a triple-sum restriction, preserving the six-or-more bucket semantics."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np;prior=ROOT/'milestones/49-six-direction-pair-catalogue'
meta=json.loads((prior/'data/model.json').read_text())
with np.load(prior/'build/graph.npz') as z:arrays={k:z[k].copy() for k in z.files}
old_excluded=arrays['excluded'].copy();old_demand=arrays['demand'].copy();extra=np.zeros(len(old_excluded),dtype=bool);required=np.zeros(len(old_excluded),dtype=old_demand.dtype);rules=[]
for i,ds in enumerate(meta['extensions']):
 positions=set()
 for start in range(3):
  piece=ds[start:start+6]
  if model.canon(piece)==(0,1,2,3,4,0):positions.add(tuple(start+j for j in [1,4,5]))
  if model.canon(piece[::-1])==(0,1,2,3,4,0):positions.add(tuple(start+6-j for j in [1,4,5]))
 if not positions:continue
 mask=arrays['direction']==i;codes=arrays['count_code'][mask];bad=np.zeros(len(codes),dtype=bool);demand=np.zeros(len(codes),dtype=old_demand.dtype)
 for ps in positions:
  values=[codes//6**(7-j)%6+1 for j in ps];deficit=np.maximum(0,13-sum(values));hidden=np.logical_or.reduce([v==6 for v in values])
  bad|=(deficit>0)&~hidden
  demand=np.maximum(demand,np.where(hidden,deficit,0)).astype(old_demand.dtype)
  rules.append(dict(directions=ds,positions=ps))
 extra[mask]=bad;required[mask]=demand
arrays['excluded']|=extra;arrays['demand']=np.maximum(old_demand,required)
np.savez_compressed(HERE/'build/graph.npz',**arrays)
meta['excluded_edges']=int(arrays['excluded'].sum());meta['remaining_edges']=int((~arrays['excluded']).sum())
meta['newly_excluded_by_triple']=int((extra&~old_excluded).sum())
meta['strengthened_retained_demands']=int(((arrays['demand']>old_demand)&~arrays['excluded']).sum());meta['triple_rules']=rules
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()}
meta['scope']='Milestone49 graph plus the triple sum at least13: exact low-count exclusions and a maximum common-window excess demand for capped counts. Complete arbitrary-snake Lean graph bridge pending.'
(HERE/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n')
print('Newly excluded:',meta['newly_excluded_by_triple'],'retained demands raised:',meta['strengthened_retained_demands'],flush=True)
analyze.HERE=HERE;analyze.main()
