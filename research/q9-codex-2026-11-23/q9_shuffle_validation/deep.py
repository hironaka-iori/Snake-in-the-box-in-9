from common import *
from itertools import combinations_with_replacement,product
from collections import Counter
import json,random
d=5;N=[{x^1<<i for i in range(d)} for x in range(32)];level=Counter();full=[]
def walk(x,occupied,w):
    level[len(w)]+=1
    if len(w)==13:full.append(tuple(w))
    for y in N[x]-occupied:
        if N[y]&occupied=={x}:walk(y,occupied|{y},w+[(x^y).bit_length()-1])
walk(0,{0},[]);assert max(level)==13
groups=[(0,1),(2,3),(4,)];rng=random.Random(20261121);stats=Counter()
with (D/'small_deep.jsonl').open('w') as out:
    for n in (13,14):
        exemplars=full if n==13 else []
        for seed in range(20):
            L=[3,4]+[1]*(n-7);rng.shuffle(L);w=list(rng.choice(full))
            if n==14:w.insert(rng.randrange(14),rng.randrange(5))
            fixed=signature(w,groups,L);possible={signature(q,groups,L) for q in exemplars};ct=Counter()
            for free3,free4 in product(combinations_with_replacement(range(3),3),combinations_with_replacement(range(3),4)):
                target=tuple(free3 if k==3 else free4 if k==4 else b for k,b in zip(L,fixed));template=[groups[g][0] for block in target for g in block]
                st,p,c=solver.solve(template,groups[:2],4,L,200000);assert st==('FOUND' if target in possible else 'UNSAT')
                if p:check(template,groups[:2],4,L,p)
                ct[st]+=1
            print(json.dumps(dict(n=n,sizes=L,fixed= fixed,status=ct)),file=out);stats.update(ct)
print(json.dumps(dict(complete_physical_Q5=level,matched=dict(stats))))
