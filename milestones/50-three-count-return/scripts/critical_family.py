"""Map all zero-slack recurrent transitions, rather than one attaining cycle."""
from pathlib import Path
import json,gzip,sys,collections
from fractions import Fraction
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
if '--screen' in sys.argv:HERE=HERE/'screen'
if '--excess' in sys.argv:HERE=HERE/'excess-screen'
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model,analyze
np=model.np;m=json.loads((HERE/'data/model.json').read_text());z=np.load(HERE/'build/graph.npz');a={k:z[k] for k in z.files};z.close();pi=np.frombuffer(gzip.decompress((HERE/'data/potential.i64.gz').read_bytes()),dtype='<i8')
ids=np.flatnonzero(~a['excluded']);U=a['U'][ids];V=a['V'][ids];W=168*a['count'][ids].astype(np.int64)+24*a['demand'][ids]+42*a['share'][ids]
mean=Fraction(json.loads((HERE/'data/analysis.json').read_text())['integer_weight_mean'])
zero=mean.denominator*W+pi[U]-pi[V]==mean.numerator;zi=ids[zero];ns,_=analyze.algorithms();keep=ns['prune'](m['states'],U[zero],V[zero]);ci=zi[keep]
# Retain only edges inside a strongly connected component, excluding connectors.
adj={};rev={}
for u,v in zip(a['U'][ci],a['V'][ci]):
 u=int(u);v=int(v);adj.setdefault(u,[]).append(v);adj.setdefault(v,[]);rev.setdefault(v,[]).append(u);rev.setdefault(u,[])
seen=set();order=[]
for root in adj:
 if root in seen:continue
 seen.add(root);stack=[(root,iter(adj[root]))]
 while stack:
  node,children=stack[-1]
  nxt=next(children,None)
  if nxt is None:order.append(node);stack.pop();continue
  if nxt not in seen:seen.add(nxt);stack.append((nxt,iter(adj[nxt])))
component={};sizes=[]
for root in reversed(order):
 if root in component:continue
 label=len(sizes);component[root]=label;stack=[root];size=0
 while stack:
  node=stack.pop();size+=1
  for nxt in rev[node]:
   if nxt not in component:component[nxt]=label;stack.append(nxt)
 sizes.append(size)
ci=ci[np.array([component[int(u)]==component[int(v)] for u,v in zip(a['U'][ci],a['V'][ci])])]
print('Zero-slack recurrent edges',len(ci),'states',len(np.unique(np.concatenate([a['U'][ci],a['V'][ci]]))),flush=True)
byshape=collections.Counter();windows=collections.Counter();allcounts=collections.Counter()
for index in ci:
 ds=m['extensions'][int(a['direction'][index])]
 counts=analyze.decode(int(a['count_code'][index]),7);byshape[''.join(map(str,ds))]+=1
 for v in counts:allcounts[v]+=1
 for start in range(3):
  word=tuple(ds[start:start+6]);cs=tuple(counts[start:start+5]);key=min((model.canon(word),cs),(model.canon(word[::-1]),cs[::-1]));windows[key]+=1
records=[dict(directions=list(ds),counts=list(cs),occurrences=n) for (ds,cs),n in windows.most_common()]
(HERE/'data/critical-family.json').write_text(json.dumps(dict(recurrent_edges=len(ci),recurrent_states=len(np.unique(np.concatenate([a['U'][ci],a['V'][ci]]))),counts=allcounts,shapes=byshape,windows=records,scope='Zero-slack edges inside strongly connected components contain every critical cycle and lie on such cycles. Counts refer to this finite graph.'),indent=2)+'\n')
np.save(HERE/'build/critical-indices.npy',ci)
print('Distinct five-centre windows',len(records),'count symbols',dict(allcounts),'top windows',records[:8],flush=True)
