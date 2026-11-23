from itertools import product
from two_insertions import solve
from search import axes,validate,D
import json,random
rng=random.Random(176593);hs=[0,0]
for i in range(260):
    pairs=[(0,1),(2,3)];s=4;w=[rng.randrange(5) for _ in range(rng.randint(1,8))];a,b=rng.choices(range(5),k=2)
    hh,kk=sorted(rng.choices(range(len(w)+1),k=2));windows=[(rng.randint(0,h),rng.randint(h,len(w))) for h in (hh,kk)]
    choices=[(4,) if c==4 else pairs[c//2] for c in w]
    sat=any(validate(axes(z[:h]+(a,)+z[h:k]+(b,)+z[k:])) for z in product(*choices) for h in range(windows[0][0],windows[0][1]+1) for k in range(max(h,windows[1][0]),windows[1][1]+1))
    st,p,_,_=solve(w,pairs,s,a,b,50000,windows)
    assert st!='UNKNOWN' and (st=='FOUND')==sat;hs[sat]+=1
print(json.dumps(dict(small=hs)),flush=True)
for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:24]):
    w=list(map(int,w));ds=list(range(9));rng.shuffle(ds);ps=[tuple(ds[j:j+2]) for j in range(0,8,2)];s=ds[-1];h,k=sorted(rng.sample(range(2,len(w)-1),2))
    a,b=w[h],w[k];w.pop(k);w.pop(h)
    for j,c in enumerate(w):
        if rng.randrange(8)==0:w[j]=rng.choice(next(g for g in [*ps,[s]] if c in g))
    st,p,seams,f=solve(w,ps,s,a,b,90000)
    print(json.dumps(dict(case=i,status=st,edges=len(p)-1 if p else None,seams=seams,path=p)),flush=True)
