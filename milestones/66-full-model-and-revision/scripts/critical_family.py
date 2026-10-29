"""Extract every tight cyclic edge, including replacement minima outside the saved cycle."""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
name='pressured';meta=json.loads((HERE/f'data/{name}-model.json').read_text());result=json.loads((HERE/f'data/{name}-analysis.json').read_text())
with np.load(HERE/f'build/{name}-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert hashlib.sha256(a[k].tobytes()).hexdigest()==h
raw=gzip.decompress((HERE/f'data/{name}-potential.i64.gz').read_bytes());assert hashlib.sha256(raw).hexdigest()==result['potential_sha256']
pi=np.frombuffer(raw,dtype='<i8');mu=Fraction(result['integer_mean']);p,d=mu.numerator,mu.denominator
slack=d*a['weight'].astype(np.int64)+pi[a['U']]-pi[a['V']]-p;assert np.all(slack>=0)
ids=np.flatnonzero(slack==0);adj={};rev={}
for u,v in zip(a['U'][ids].tolist(),a['V'][ids].tolist()):
    adj.setdefault(u,[]).append(v);adj.setdefault(v,[])
    rev.setdefault(v,[]).append(u);rev.setdefault(u,[])
seen=set();order=[]
for root in adj:
    if root in seen:continue
    seen.add(root);stack=[(root,iter(adj[root]))]
    while stack:
        v,it=stack[-1];w=next(it,None)
        if w is None:order.append(v);stack.pop()
        elif w not in seen:seen.add(w);stack.append((w,iter(adj[w])))
component={};label=0
for root in reversed(order):
    if root in component:continue
    component[root]=label;stack=[root]
    while stack:
        v=stack.pop()
        for w in rev[v]:
            if w not in component:component[w]=label;stack.append(w)
    label+=1
ids=ids[np.array([component[int(u)]==component[int(v)] for u,v in zip(a['U'][ids],a['V'][ids])])]
SOURCE=ROOT/'milestones/59-extended-share-window/extended';sm=json.loads((SOURCE/'data/model.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z:s={k:z[k] for k in ['direction','count_code']}
nodes=collections.defaultdict(set);ec=collections.Counter();rows=[]
for i in ids:
    u,v=int(a['U'][i]),int(a['V'][i]);c=component[u];nodes[c].update([u,v]);ec[c]+=1
    e=int(a['source_edge'][i]);code=int(s['count_code'][e]);counts=[code//6**j%6+1 for j in range(5,-1,-1)]
    rows.append(dict(edge=int(i),u=u,v=v,component=c,history=int(a['history'][i]),
        directions=sm['extensions'][int(s['direction'][e])],counts=counts,weight=int(a['weight'][i])))
summary=dict(status='EXACT_FINITE_CRITICAL_FAMILY',integer_mean=str(mu),critical_states=len(set(a['U'][ids].tolist()+a['V'][ids].tolist())),
    critical_edges=len(ids),components=[dict(id=c,states=len(nodes[c]),edges=ec[c]) for c in sorted(ec)],
    potential_sha256=result['potential_sha256'],scope='All tight cyclic edges of the recorded finite model; no global snake bound or Lean replay of this extraction.')
(HERE/'data/critical-edges.json').write_text(json.dumps(rows,indent=2)+'\n')
(HERE/'data/critical-family.json').write_text(json.dumps(summary,indent=2)+'\n');print(summary)
