"""Extract critical edges using an exact potential; select windows on the saved cycle."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,json,sys
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np;folder=HERE/'exploratory-share'
meta=json.loads((folder/'data/model.json').read_text());result=json.loads((folder/'data/analysis.json').read_text())
with np.load(folder/'build/graph.npz') as z:a={k:z[k] for k in z.files}
pi=np.frombuffer(gzip.decompress((folder/'data/potential.i64.gz').read_bytes()),dtype='<i8')
mean=Fraction(result['integer_weight_mean']);ids=np.flatnonzero(~a['excluded']);U=a['U'][ids];V=a['V'][ids]
W=336*a['count'][ids].astype(np.int64)+48*a['demand'][ids]+42*a['share'][ids]+a['share_lower'][ids]
assert np.all(mean.numerator+pi[V]<=mean.denominator*W+pi[U])
ids=ids[mean.denominator*W+pi[U]-pi[V]==mean.numerator]
adj={};rev={}
for u,v in zip(a['U'][ids].tolist(),a['V'][ids].tolist()):
 adj.setdefault(u,[]).append(v);adj.setdefault(v,[]);rev.setdefault(v,[]).append(u);rev.setdefault(u,[])
seen=set();order=[]
for root in adj:
 if root in seen:continue
 seen.add(root);stack=[(root,iter(adj[root]))]
 while stack:
  node,children=stack[-1];nxt=next(children,None)
  if nxt is None:order.append(node);stack.pop()
  elif nxt not in seen:seen.add(nxt);stack.append((nxt,iter(adj[nxt])))
comp={};label=0
for root in reversed(order):
 if root in comp:continue
 comp[root]=label;stack=[root]
 while stack:
  node=stack.pop()
  for nxt in rev[node]:
   if nxt not in comp:comp[nxt]=label;stack.append(nxt)
 label+=1
ids=ids[np.array([comp[int(u)]==comp[int(v)] for u,v in zip(a['U'][ids],a['V'][ids])])]
def windows(ds,cs):
 for start in range(3):
  word=ds[start:start+6];counts=tuple(cs[start:start+5])
  yield min((model.canon(word),counts),(model.canon(word[::-1]),counts[::-1]))
allwins=collections.Counter();cyclewins=collections.Counter()
for i in ids:allwins.update(windows(meta['extensions'][int(a['direction'][i])],analyze.decode(int(a['count_code'][i]),7)))
for r in result['cycle']:cyclewins.update(windows(r['directions'],r['counts']))
rows=[dict(directions=list(ds),counts=list(cs),occurrences=n,cycle_occurrences=cyclewins[(ds,cs)]) for (ds,cs),n in allwins.most_common()]
cycle=[r for r in rows if r['cycle_occurrences']]
out=dict(edges=len(ids),states=len(set(a['U'][ids].tolist()+a['V'][ids].tolist())),windows=rows,cycle_windows=cycle)
(HERE/'data/critical-family.json').write_text(json.dumps(out,indent=2)+'\n')
print('Critical edges',len(ids),'states',out['states'],'windows',len(rows),'saved-cycle windows',len(cycle),flush=True)
