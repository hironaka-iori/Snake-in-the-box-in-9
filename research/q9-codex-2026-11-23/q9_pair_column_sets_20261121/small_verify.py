from enhanced import solve,split
from collections import Counter
import itertools,random,json
rng=random.Random(78139)
V=set(range(16));edges={v:{v^(1<<d) for d in range(4)} for v in V}
paths={}
for mask in range(1,1<<16):
    chosen={v for v in V if mask>>v&1}
    if len(chosen)<3:continue
    deg={v:edges[v]&chosen for v in chosen}
    tips=[v for v,n in deg.items() if len(n)==1]
    if len(tips)!=2 or any(len(t) not in (1,2) for t in deg.values()):continue
    p=[tips[0]]
    while extra:=deg[p[-1]]-set(p):p.append(extra.pop())
    if len(p)==len(chosen):paths[mask]=p
population=list(paths.values());by={}
for p in population:by.setdefault(len(p),[]).append(p)
out=Counter()
for i in range(90):
    p=rng.choice(population);aa=rng.sample(range(4),2);orig=[split(p,a) for a in aa]
    us=[set(rng.sample(sorted(split(V,a)),rng.randrange(2,9))) for a in aa]
    n=rng.randrange(4,11);must=bool(i%2);expected=any(all(split(q,a)-u==o-u and (not must or split(q,a)!=o) for a,u,o in zip(aa,us,orig)) for q in by.get(n,()))
    status=solve(p,aa,us,n,20000,require_new=must)['status']
    assert (status=='FOUND')==expected and status!='UNKNOWN',(i,status,expected)
    out[status]+=1
print(json.dumps(dict(exhaustive_vertex_subsets=65535,pathsets=len(paths),cases=90,results=out)))
