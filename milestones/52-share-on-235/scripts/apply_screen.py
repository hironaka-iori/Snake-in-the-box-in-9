"""Apply only the five new numerical share bounds, then check the full graph."""
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np;prior=HERE/'exploratory-share';folder=HERE/'cycle-share'
(folder/'data').mkdir(parents=True,exist_ok=True);(folder/'build').mkdir(exist_ok=True)
meta=json.loads((prior/'data/model.json').read_text());rules=[r for r in json.loads((HERE/'data/share-screen.json').read_text()) if r['status']=='INFEASIBLE']
with np.load(prior/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
before=a['share_lower'].copy()
for di,ds in enumerate(meta['extensions']):
 mask=a['direction']==di;codes=a['count_code'][mask];q=a['share_lower'][mask].copy()
 cs=np.stack([codes//6**(6-j)%6+1 for j in range(7)],axis=1)
 for start in range(3):
  for reverse in [False,True]:
   word=ds[start:start+6];sub=cs[:,start:start+5];shape=model.canon(word[::-1] if reverse else word);sub=sub[:,::-1] if reverse else sub
   for row in rules:
    if shape==tuple(row['dirs']):q=np.maximum(q,np.where(np.all(sub==row['counts'],axis=1),96,0))
 a['share_lower'][mask]=q
meta['new_rules']=rules;meta['newly_strengthened_edges']=int(((a['share_lower']>before)&~a['excluded']).sum())
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
meta['scope']='Exploratory graph with five additional unreplayed share bounds. No global theorem.'
(folder/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n');np.savez_compressed(folder/'build/graph.npz',**a)
print('Additional strengthened edges',meta['newly_strengthened_edges'],flush=True)
analyze_share.HERE=folder;analyze_share.main()
