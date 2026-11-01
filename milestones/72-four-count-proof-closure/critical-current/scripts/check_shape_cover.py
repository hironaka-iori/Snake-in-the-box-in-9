"""Exhaust every subset of critical direction shapes using topological deletion."""
from pathlib import Path
from collections import Counter,defaultdict,deque
import hashlib,itertools,json
HERE=Path(__file__).resolve().parents[1]
source=HERE/'data/critical-edges.json';edges=json.loads(source.read_text())
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
def shape(e):
 w=e['directions'][-6:];return min(canon(w),canon(w[::-1]))
shapes=sorted({shape(e) for e in edges});ix={s:i for i,s in enumerate(shapes)}
indexed=[(e['u'],e['v'],ix[shape(e)]) for e in edges]
nodes={v for u,v,s in indexed}|{u for u,v,s in indexed}
def acyclic(mask):
 deg={u:0 for u in nodes};out=defaultdict(list)
 for u,v,s in indexed:
  if mask>>s&1:continue
  deg[v]+=1;out[u].append(v)
 q=deque(u for u in nodes if not deg[u]);removed=0
 while q:
  u=q.popleft();removed+=1
  for v in out[u]:
   deg[v]-=1
   if not deg[v]:q.append(v)
 return removed==len(nodes)
truth={m:acyclic(m) for m in range(1<<len(shapes))}
minimal=[m for m,ok in truth.items() if ok and all(not truth[m^(1<<i)] for i in range(len(shapes)) if m>>i&1)]
result=dict(status='EXHAUSTIVE_FINITE_SHAPE_COVER',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),edges=len(edges),states=len(nodes),shapes=[dict(directions=list(s),edges=sum(t==i for u,v,t in indexed)) for i,s in enumerate(shapes)],subsets_checked=len(truth),minimal_covers=[[list(shapes[i]) for i in range(len(shapes)) if m>>i&1] for m in minimal],acyclic_by_mask=truth,scope='Exact calculation on saved tight critical graph. Positive extra weight on a cover strictly raises its finite minimum mean; this supplies no numerical global bound.')
(HERE/'data/shape-cover.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='acyclic_by_mask'})
