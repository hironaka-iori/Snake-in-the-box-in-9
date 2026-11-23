from switching import solve
from search import validate,axes,D
from itertools import product
import random,json
rng=random.Random(349713);small=[0,0]
for i in range(300):
    n=rng.randrange(3,12);d=rng.randrange(3,7);w=[rng.randrange(d) for _ in range(n)];alt=[rng.randrange(d) for _ in range(n)]
    expected=any(validate(axes(z)) for z in product(*[set(z) for z in zip(w,alt)]))
    st,p,k=solve(w,alt,10000)
    assert (st=='FOUND')==expected and st!='UNKNOWN';small[expected]+=1
print(json.dumps(dict(small=small)),flush=True)
for i,line in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:24]):
    w=list(map(int,line));alts=[]
    # Both supplied orientations are corrupted; the original remains in each position's alternatives.
    a=w.copy();b=w.copy()
    for j,c in enumerate(w):
        other=rng.randrange(9)
        if rng.getrandbits(1):a[j]=other
        else:b[j]=other
    assert not validate(axes(a)) and not validate(axes(b))
    st,p,k=solve(a,b,100000,a)
    print(json.dumps(dict(case=i,status=st,edges=len(p)-1 if p else None,path=p)),flush=True)
    assert p and validate(p) and len(p)==192
