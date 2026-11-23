from buckets import run
from search import axes,validate,D
from itertools import product
import random,json
rng=random.Random(113792);cnt=[0,0]
for _ in range(280):
    dims=list(range(5));rng.shuffle(dims);k=rng.choice([2,3,4]);groups=[tuple(dims[:k]),tuple(dims[k:])]
    w=[rng.randrange(5) for _ in range(rng.randint(3,9))];allowed=[next(g for g in groups if c in g) for c in w]
    sat=any(validate(axes(p)) for p in product(*allowed));st,p,_=run(w,groups,60000)
    assert st!='UNKNOWN' and (st=='FOUND')==sat;cnt[sat]+=1
print(json.dumps(dict(exhaustive=sum(cnt),feasible=cnt[1],infeasible=cnt[0])),flush=True)
for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:16]):
    w=list(map(int,w));ds=list(range(9));rng.shuffle(ds);groups=[tuple(ds[:3]),tuple(ds[3:5]),tuple(ds[5:7]),tuple(ds[7:])]
    for j,c in enumerate(w):
        if rng.randrange(7)==0:w[j]=rng.choice(next(g for g in groups if c in g))
    assert not validate(axes(w));st,p,k=run(w,groups,150000)
    print(json.dumps(dict(case=i,status=st,edges=len(p)-1 if p else None,path=p)),flush=True)
    assert p and len(p)==192 and validate(p)
