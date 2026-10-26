"""Apply common-window share bounds with the checked mixed-charge budget."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
import analyze_share
np=model.np;prior=HERE/'pass5';folder=HERE/'share-model';(folder/'data').mkdir(parents=True,exist_ok=True);(folder/'build').mkdir(exist_ok=True)
meta=json.loads((prior/'data/model.json').read_text());rows=json.loads((HERE/'data/share-screen.json').read_text());rules=[r for r in rows if r['status']=='INFEASIBLE']
with np.load(prior/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
q=np.zeros(len(a['U']),dtype=np.int64)
for i,ds in enumerate(meta['extensions']):
 mask=a['direction']==i;codes=a['count_code'][mask];req=q[mask].copy()
 for start in range(3):
  for reverse in [False,True]:
   word=ds[start:start+6];shape=model.canon(word[::-1] if reverse else word)
   for row in rules:
    if shape!=tuple(row['dirs']):continue
    hit=np.ones(len(codes),dtype=bool)
    for j,c in enumerate(row['counts'],1):
     p=start+6-j if reverse else start+j;hit&=(codes//6**(7-p)%6+1)==c
    req=np.maximum(req,np.where(hit,row['cap']+1,0))
 q[mask]=req
a['share_lower']=q;meta['share_rules']=rules;meta['share_strengthened_edges']=int(((q>0)&~a['excluded']).sum());meta['weight_scale']=336
meta['scope']='Exploratory mixed-charge graph, conditioned on unreplayed share and earlier count exclusions. No new global theorem.'
meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
(folder/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n');np.savez_compressed(folder/'build/graph.npz',**a)
print('Share bounds',len(rules),'strengthened edges',meta['share_strengthened_edges'],flush=True)
analyze_share.HERE=folder;analyze_share.main()
