from anywhere import *
from itertools import product
import random
def oracle(w,d):
    # Enumerate a tiling directly from its left end, extending actual physical vertices.
    def grow(t,chosen,tip):
        if t==len(w):return True
        for k in (1,3,4):
            if t+k>len(w):continue
            for v in set(permutations(w[t:t+k])):
                occ=chosen.copy();u=tip
                for a in v:
                    y=u^(1<<a)
                    if y in occ or any(q!=u and (q^y).bit_count()==1 for q in occ):break
                    occ.add(y);u=y
                else:
                    if grow(t+k,occ,u):return True
        return False
    return grow(0,{0},0)
stats=Counter();rng=random.Random(71239)
for d,n,ws in [(3,n,product(range(3),repeat=n)) for n in range(7)]+[(5,n,[tuple(rng.randrange(5) for _ in range(n)) for j in range(100)]) for n in range(4,12)]:
    for w in ws:
        w=list(w);yes=oracle(w,d);st,c,p,u=unrestricted(w,100000);assert st==('FOUND' if yes else 'UNSAT'),w;stats[d,st]+=1
        if p:assert induced(p,d)
print(json.dumps({str(k):v for k,v in stats.items()}))
