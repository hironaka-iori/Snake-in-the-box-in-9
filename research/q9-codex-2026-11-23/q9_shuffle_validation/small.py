from itertools import combinations_with_replacement,product
from collections import Counter
import json
from common import *
def paths(d,n):
    N=[[v^1<<a for a in range(d)] for v in range(1<<d)];seen={0};w=[]
    def grow(v):
        if len(w)==n:yield tuple(w);return
        for a,x in enumerate(N[v]):
            if x in seen or any(y in seen and y!=v for y in N[x]):continue
            seen.add(x);w.append(a);yield from grow(x);w.pop();seen.remove(x)
    yield from grow(0)
def profiles(n):
    if not n:yield ()
    else:
        for k in range(1,min(n,4)+1):
            for v in profiles(n-k):yield (k,)+v
summary=Counter()
with (D/'small.jsonl').open('w') as out:
    for d,nmax in ((3,7),(5,6)):
        pairs=[(i,i+1) for i in range(0,d-1,2)];single=d-1;G=[*pairs,(single,)];ng=len(G)
        for n in range(nmax+1):
            physical=list(paths(d,n))
            for lengths in profiles(n):
                yes={signature(w,G,lengths) for w in physical};ct=Counter()
                for blocks in product(*(combinations_with_replacement(range(ng),k) for k in lengths)):
                    w=[G[g][0] for b in blocks for g in b]
                    st,p,conf=solver.solve(w,pairs,single,lengths,100000)
                    assert st==('FOUND' if blocks in yes else 'UNSAT'),(d,n,lengths,blocks,st)
                    if p:check(w,pairs,single,lengths,p)
                    ct[st]+=1
                summary.update(ct);print(json.dumps(dict(dim=d,n=n,sizes=lengths,physical=len(physical),truth=len(yes),rows=ct)),file=out)
print(json.dumps(summary))
