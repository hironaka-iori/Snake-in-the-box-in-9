"""Independent full-cube census and local-forest checks of the saved feasible window."""
from pathlib import Path
from itertools import combinations
import json
HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/general-one-cap0.json').read_text());assert r['status']=='SAT'
S=set(r['selected']);path=[0]
for d in r['directions']:path.append(path[-1]^(1<<d))
assert len(set(path))==len(path) and set(path)<=S
centres=path[1:-1];B={x for x in range(512) if min((x^c).bit_count() for c in centres)<=4};assert S<=B
neighbors=lambda v:[v^(1<<a) for a in range(9)]
degree={v:len(set(neighbors(v))&S) for v in range(512)}
assert all(degree[v]<=2 for v in S)
interior={v for v in S if set(neighbors(v))<=B}
assert all(degree[v]>=1 for v in interior)
assert sum(degree[v]==1 for v in interior)<=2
unseen=set(S);components=[]
while unseen:
    stack=[next(iter(unseen))];vertices=set()
    while stack:
        v=stack.pop()
        if v not in unseen:continue
        unseen.remove(v);vertices.add(v);stack.extend(set(neighbors(v))&unseen)
    edges=sum(degree[v] for v in vertices)//2
    assert edges==len(vertices)-1
    components.append(len(vertices))
pairs=list(combinations(range(9),2));empty={}
for q in range(512):
    empty[q]=sum(not (S&{q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}) for a,b in pairs)
alpha=[sum(not (S&{c^(1<<a),c^(1<<b),c^(1<<a)^(1<<b)}) for a,b in pairs) for c in centres]
share=[sum(12*empty[q]//degree[q] for q in neighbors(c) if degree[q]) for c in centres]
assert all(lo<=x<=hi for x,(lo,hi) in zip(alpha,r['bounds']))
assert alpha==r['census']['alpha'] and share==r['census']['share'] and sum(share)==r['census']['total_share']
out=dict(status='PASS',vertices=len(S),component_sizes=sorted(components),counts=alpha,shares=share,total_share=sum(share),scope='Local acyclic witness, with complete-neighborhood endpoint budget checked. Extension to a complete snake is unproved.')
(HERE/'data/one-zero-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
