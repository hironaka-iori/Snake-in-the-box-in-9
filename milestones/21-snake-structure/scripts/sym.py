import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from common import *
from bankwalk import quotient
from itertools import permutations
from collections import Counter
b=load()
def auts(k):
    out=[]
    for p in permutations(range(k)):
        for t in range(1<<k):
            out.append([sum(((x>>i)&1)<<p[i] for i in range(k))^t for x in range(1<<k)])
    return out
A5=auts(5); A4=auts(4)
res=Counter()
for idx in list(range(0,127,6)):
    e=b[idx]; vs=e['vertex_sequence']; seq,sizes,L,H=quotient(e,4)
    def cell(v): return sum(((v>>c)&1)<<i for i,c in enumerate(L))
    def hv(v): return sum(((v>>c)&1)<<i for i,c in enumerate(H))
    T={x:set() for x in range(32)}
    for v in vs: T[hv(v)].add(cell(v))
    A=frozenset(x for x in range(32) if all(pc(c)%2==0 for c in T[x]) and T[x])
    B=frozenset(x for x in range(32) if all(pc(c)%2==1 for c in T[x]) and T[x])
    S=set((hv(v),cell(v)) for v in vs)
    best=0; bestg=None
    for s in A5:
        if frozenset(s[x] for x in A)!=B: continue
        for t in A4:
            ov=sum(1 for (x,c) in S if (s[x],t[c]) in S)
            if ov>best: best=ov; bestg=(s,t)
    # also best overall with sigma fixing A (A->A)
    print(idx,'|A|,|B|',len(A),len(B),'max overlap of S with g(S) for g swapping A,B:',best, flush=True)
