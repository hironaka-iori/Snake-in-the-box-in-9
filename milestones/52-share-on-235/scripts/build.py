"""Apply pinned 235 exclusions and compare certified and exploratory share charges."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
sys.path.insert(0,str(ROOT/'milestones/51-exact-bucket-pressure/scripts'))
import analyze_share
np=model.np
REF='74ca83db9c218446211d4f24c5e5a07329fdd847'
PATH='milestones/23-k6-lean/full_product/keys_235.json'
(HERE/'data').mkdir(parents=True,exist_ok=True)
raw=subprocess.check_output(['git','-c','core.commitGraph=false','show',REF+':'+PATH],cwd=ROOT)
(HERE/'data/keys_235.json').write_bytes(raw)
keys=json.loads(raw)['keys'];assert len(keys)==1287
tables={}
for ds,bounds in keys:
 cs=[]
 for lo,hi in bounds:
  assert (lo==hi and 1<=lo<=5) or (lo==6 and hi==21)
  cs.append(lo)
 for word,counts in [(ds,cs),(ds[::-1],cs[::-1])]:
  table=tables.setdefault(model.canon(word),np.zeros(6**len(cs),dtype=bool))
  table[int(model.code(np.array([counts]))[0])]=True
combined='--combined' in sys.argv
prior=ROOT/('milestones/51-exact-bucket-pressure/pass5' if combined else 'milestones/50-three-count-return')
meta=json.loads((prior/'data/model.json').read_text())
with np.load(prior/'build/graph.npz') as z:a={k:z[k].copy() for k in z.files}
old=a['excluded'].copy();q=np.zeros(len(a['U']),dtype=np.int64);qe=q.copy()
rules=json.loads((ROOT/'milestones/51-exact-bucket-pressure/data/share-screen.json').read_text())
rules=[r for r in rules if r['status']=='INFEASIBLE']
for di,ds in enumerate(meta['extensions']):
 mask=a['direction']==di;codes=a['count_code'][mask]
 cs=np.stack([codes//6**(6-j)%6+1 for j in range(7)],axis=1)
 bad=a['excluded'][mask].copy();lower=q[mask].copy();extra=qe[mask].copy()
 for k in range(2,7):
  for start in range(8-k):
   table=tables.get(model.canon(ds[start:start+k+1]))
   if table is not None:bad|=table[model.code(cs[:,start:start+k])]
 for start in range(3):
  for reverse in [False,True]:
   word=ds[start:start+6];sub=cs[:,start:start+5]
   shape=model.canon(word[::-1] if reverse else word);sub=sub[:,::-1] if reverse else sub
   if shape==(0,1,2,3,1,4):lower=np.maximum(lower,np.where(np.all(sub==[3,3,3,6,5],axis=1),48,0))
   for row in rules:
    if shape==tuple(row['dirs']):extra=np.maximum(extra,np.where(np.all(sub==row['counts'],axis=1),96,0))
 a['excluded'][mask]=bad;q[mask]=lower;qe[mask]=extra
print('Contributor keys removed',int((a['excluded']&~old).sum()),'further edges; retained',int((~a['excluded']).sum()),flush=True)
meta['contributor_exclusions']=dict(ref=REF,path=PATH,sha256=hashlib.sha256(raw).hexdigest(),keys=len(keys))
meta['remaining_edges']=int((~a['excluded']).sum());meta['excluded_edges']=int(a['excluded'].sum())
for name,charge in ([('combined-share',np.maximum(q,qe))] if combined else [('checked-share',q),('exploratory-share',np.maximum(q,qe))]):
 folder=HERE/name;(folder/'data').mkdir(parents=True,exist_ok=True);(folder/'build').mkdir(exist_ok=True)
 a['share_lower']=charge;meta['share_strengthened_edges']=int(((charge>0)&~a['excluded']).sum())
 meta['arrays_sha256']={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()}
 meta['scope']='Finite graph using contributor-checked count exclusions and '+('Lean-checked share48' if name=='checked-share' else 'unreplayed share96')+(' plus previously saved numerical count/excess premises' if combined else '')+'. Full local graph-to-snake proof pending; no new global bound.'
 (folder/'data/model.json').write_text(json.dumps(meta,indent=2)+'\n');np.savez_compressed(folder/'build/graph.npz',**a)
 print(name,'positive-share edges',meta['share_strengthened_edges'],flush=True)
 analyze_share.HERE=folder;analyze_share.main()
