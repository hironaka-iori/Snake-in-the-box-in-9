from ordered_end import solve
from search import axes,validate,D
from itertools import product
import random,json
rng=random.Random(184929);hist=[0,0]
for _ in range(240):
    w=[rng.randrange(5) for _ in range(2*rng.randrange(1,5)+1)];groups=[(0,1),(2,3),(4,)];blocks=[]
    for j in range(0,len(w)-1,2):
        a,b=[next(g for g in groups if d in g) for d in w[j:j+2]]
        choices=set(product(a,b))|set(product(b,a));blocks.append(choices)
    sat=any(validate(axes([v for pair in variant for v in pair]+[last])) for variant in product(*blocks) for last in next(g for g in groups if w[-1] in g));st,p,k=solve(w,groups[:2],4,50000)
    assert st!='UNKNOWN' and (st=='FOUND')==sat;hist[sat]+=1
print(json.dumps(dict(small=hist)),flush=True)
for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:24]):
    w=list(map(int,w[:191]));dims=list(range(9));rng.shuffle(dims);ps=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1]
    for t in range(0,len(w)-1,2):
        if rng.getrandbits(1):w[t],w[t+1]=w[t+1],w[t]
        for h in [t,t+1]:
            for g in ps:
                if w[h] in g and rng.randrange(5)==0:w[h]=g[0]^g[1]^w[h];break
    assert not validate(axes(w));st,p,k=solve(w,ps,s,120000)
    print(json.dumps(dict(case=i,status=st,edges=len(p)-1 if p else None,witness=p)),flush=True)
