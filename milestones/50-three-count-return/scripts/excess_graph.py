"""Measure simultaneous ordinary exclusions and forced hidden count excess."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np;prior=HERE/'screen';target=HERE/'excess-screen'
(target/'build').mkdir(parents=True,exist_ok=True);(target/'data').mkdir(exist_ok=True)
meta=json.loads((prior/'data/model.json').read_text());rows=json.loads((HERE/'data/excess-survey.json').read_text())
rules=[r for r in rows if r['status']=='UNSAT']
with np.load(prior/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
old=a['demand'].copy()
for i,ds in enumerate(meta['extensions']):
 mask=a['direction']==i;codes=a['count_code'][mask];req=a['demand'][mask].copy()
 for start in range(3):
  for rev in [False,True]:
   word=ds[start:start+6];canon=model.canon(word[::-1] if rev else word)
   for row in rules:
    if canon!=tuple(row['directions']):continue
    applies=np.ones(len(codes),dtype=bool)
    for j,c in enumerate(row['counts'],1):
     position=start+6-j if rev else start+j;value=codes//6**(7-position)%6+1
     applies&=(value==6) if c==6 else (value<=c)
    req=np.maximum(req,np.where(applies,row['excess_cap']+1,0))
 a['demand'][mask]=req
meta.update(excess_rules=rules,strengthened_screen_demands=int(((a['demand']>old)&~a['excluded']).sum()))
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
meta['scope']='Exploratory graph using solver exclusions and forced hidden excess. All new premises need proof replay and geometric interpretation.'
(target/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n');np.savez_compressed(target/'build/graph.npz',**a)
print('Raised retained demands',meta['strengthened_screen_demands'],flush=True)
analyze.HERE=target;analyze.main()
