from itertools import product
from domains import solve
from switching import solve as two_solve
from search import axes,validate,D
import random,json
rng=random.Random(152103);cnt=[0,0]
for _ in range(160):
    n=rng.randint(3,9);d=rng.randrange(3,6);dom=[set(rng.sample(range(d),rng.randint(1,min(d,3)))) for j in range(n)]
    w=[next(iter(g)) for g in dom];sat=any(validate(axes(z)) for z in product(*dom));st,p,k=solve(w,dom,50000)
    assert st!='UNKNOWN' and (st=='FOUND')==sat;cnt[sat]+=1
print(json.dumps(dict(small=cnt)),flush=True)
for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:24]):
    w=list(map(int,w));u=rng.randrange(30,160);ds=list(range(9));rng.shuffle(ds);m={ds[j]:ds[j^1] if j<8 else ds[j] for j in range(9)};ds2=ds.copy();rng.shuffle(ds2);m2={ds2[j]:ds2[j^1] if j<8 else ds2[j] for j in range(9)}
    sets=[{a,(m if j<u or j>=u+10 else m2)[a]} for j,a in enumerate(w)]
    aa=[next(iter(s-{a}),a) if j%5==0 else a for j,(a,s) in enumerate(zip(w,sets))];bb=[next(iter(s-{a}),a) for a,s in zip(aa,sets)]
    st,p,_=two_solve(aa,bb,100000,aa);print(json.dumps(dict(case=i,mode='switch',status=st,edges=len(p)-1 if p else None)),flush=True)
    for j in range(u-2,u+2):sets[j].update(rng.sample(range(9),4))
    st,q,_=solve(aa,sets,100000);print(json.dumps(dict(case=i,mode='domains',status=st,edges=len(q)-1 if q else None,path=q)),flush=True)
    if p:assert validate(p)
    if q:assert validate(q)
