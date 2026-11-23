from search import lift,axes,validate,D
from itertools import product
import json,random
rng=random.Random(93521)
small=[]
for _ in range(350):
    pairs=((0,1),(2,3));w=[rng.randrange(5) for _ in range(rng.randrange(3,13))]
    choices=[(4,) if c==4 else pairs[c//2] for c in w]
    sat=any(validate(axes(z)) for z in product(*choices))
    st,p,_=lift(w,pairs,4,50000)
    assert (st=='FOUND')==sat and st!='UNKNOWN'
    small.append(sat)
print(json.dumps(dict(small=len(small),feasible=sum(small),infeasible=small.count(False))),flush=True)
words=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
for i in range(32):
    w=list(map(int,words[(i*11)%len(words)]));dims=list(range(9));rng.shuffle(dims);ps=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1]
    for j,c in enumerate(w):
        for a,b in ps:
            if c in (a,b) and rng.randrange(6)==0:w[j]=a^b^c;break
    assert not validate(axes(w))
    st,p,k=lift(w,ps,s,100000)
    print(json.dumps(dict(case=i,status=st,conflicts=k,edges=len(p)-1 if p else None,path=p)),flush=True)
    assert st=='FOUND' and validate(p)
