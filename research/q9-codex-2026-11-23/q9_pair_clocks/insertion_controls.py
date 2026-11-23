from itertools import product
from search import axes,validate,D
from insertion import solve
import random,json
rng=random.Random(757914);small=[]
for _ in range(300):
    ps=((0,1),(2,3));s=4;e=rng.randrange(3);w=[rng.randrange(5) for i in range(rng.randint(2,10))]
    lo=rng.randrange(len(w)+1);hi=rng.randint(lo,len(w))
    choices=[(4,) if c==4 else ps[c//2] for c in w];b=4 if e==2 else ps[e][1]
    ok=any(validate(axes(z[:h]+(b,)+z[h:])) for z in product(*choices) for h in range(lo,hi+1))
    st,p,h,c=solve(w,ps,s,e,50000,(lo,hi));assert st!='UNKNOWN' and (st=='FOUND')==ok
    small.append(ok)
print(json.dumps(dict(exhaustive=len(small),feasible=sum(small))),flush=True)
src=(D.parent/'q9_gap_generations/prior191.words').read_text().split()
for i in range(24):
    w=list(map(int,src[i]));dim=list(range(9));rng.shuffle(dim);ps=[tuple(dim[j:j+2]) for j in range(0,8,2)];single=dim[8]
    h=rng.randrange(1,len(w)-1);c=w.pop(h);e=next((i for i,z in enumerate(ps) if c in z),4)
    for j,d in enumerate(w):
        for a,b in ps:
            if d in (a,b) and rng.randrange(5)==0:w[j]=a^b^d;break
    out,p,found_h,k=solve(w,ps,single,e,75000);print(json.dumps(dict(case=i,status=out,returned=found_h,deleted=h,edges=len(p)-1 if p else None,path=p)),flush=True)
    assert p and validate(p) and len(p)==192
