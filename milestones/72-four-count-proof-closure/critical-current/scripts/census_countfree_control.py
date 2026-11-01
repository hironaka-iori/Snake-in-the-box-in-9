"""Independent census of the cap-15 SAT relaxation, including its cyclic defect."""
from pathlib import Path
from itertools import combinations
import json
HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/general3-cap15-certificate.json').read_text());assert r['status']=='SAT_LOCAL_RELAXATION'
S=set(r['selected']);path=[0]
for d in r['directions']:path.append(path[-1]^(1<<d))
assert len(set(path))==len(path) and set(path)<=S
centres=path[1:-1];B={x for x in range(512) if min((x^c).bit_count() for c in centres)<=4};assert S<=B
neighbors=lambda v:{v^(1<<a) for a in range(9)}
degree={v:len(neighbors(v)&S) for v in range(512)};assert all(degree[v]<=2 for v in S)
interior={v for v in S if neighbors(v)<=B}
assert all(degree[v]>=1 for v in interior) and sum(degree[v]==1 for v in interior)<=2
unseen=set(S);components=[];cycles=[]
while unseen:
 stack=[min(unseen)];vertices=set()
 while stack:
  v=stack.pop()
  if v not in unseen:continue
  unseen.remove(v);vertices.add(v);stack.extend(neighbors(v)&unseen)
 edge_count=sum(degree[v] for v in vertices)//2
 assert edge_count in [len(vertices)-1,len(vertices)]
 components.append(dict(vertices=len(vertices),edges=edge_count))
 if edge_count==len(vertices):cycles.append(sorted(vertices))
pairs=list(combinations(range(9),2))
empty={q:sum(not(S&{q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}) for a,b in pairs) for q in range(512)}
alpha=[sum(not(S&{c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)}) for a,b in pairs) for c in centres]
shares=[sum(12*empty[q]//degree[q] for q in neighbors(c) if degree[q]) for c in centres]
assert sum(shares)<=15 and cycles
out=dict(status='PASS_CYCLIC_RELAXATION_CONTROL',vertices=len(S),counts=alpha,shares=shares,total_share=sum(shares),components=components,cycles=cycles,scope='SAT configuration passes degree and local endpoint constraints but contains cycles. It is not a snake or an acyclic local witness; it does not disprove a universal snake inequality.')
(HERE/'data/cap15-cyclic-control.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['components','cycles']},'cycles',len(cycles),[len(c) for c in cycles])
