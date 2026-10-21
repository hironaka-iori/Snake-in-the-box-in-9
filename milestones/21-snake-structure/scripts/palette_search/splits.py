"""Palettes of the Q8 record for every choice of heavy coordinates."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import json,itertools
from collections import Counter
w=json.load(open(_os.path.join(REPO, 'outputs', 'snake8_witness.json')))
vs=w['vertex_sequence']
pc=lambda x: bin(x).count('1')
def palette(vs,n,H):
    L=[c for c in range(n) if c not in H]
    cell=lambda v: sum(((v>>c)&1)<<i for i,c in enumerate(L))
    hv=lambda v: sum(((v>>c)&1)<<i for i,c in enumerate(H))
    T={x:set() for x in range(1<<len(H))}
    for v in vs: T[hv(v)].add(cell(v))
    A=sorted(x for x in T if T[x] and all(pc(c)%2==0 for c in T[x]))
    B=sorted(x for x in T if T[x] and all(pc(c)%2==1 for c in T[x]))
    trans_ok=all(hv(a) not in A and hv(a) not in B for a,b in zip(vs,vs[1:]) if cell(a)!=cell(b))
    walk=[];
    for v in vs:
        c=cell(v)
        if not walk or walk[-1]!=c: walk.append(c)
    return A,B,walk
def forest(S,h):
    S=set(S)
    deg=[sum((x^(1<<d)) in S for d in range(h)) for x in S]
    if max(deg,default=0)>2: return False
    # acyclic: edges = |S| - components
    E=sum(deg)//2; seen=set(); comp=0
    for s in S:
        if s in seen: continue
        comp+=1; st=[s]; seen.add(s)
        while st:
            u=st.pop()
            for d in range(h):
                v=u^(1<<d)
                if v in S and v not in seen: seen.add(v); st.append(v)
    return E==len(S)-comp
if __name__=='__main__':
    import sys
    h=int(sys.argv[1]); res=[]
    for H in itertools.combinations(range(8),h):
        A,B,walk=palette(vs,8,list(H))
        res.append(dict(H=list(H),nA=len(A),nB=len(B),forest=forest(A,h) and forest(B,h),visits=len(walk),A=A,B=B))
    res.sort(key=lambda r:-(r['nA']+r['nB']))
    for r in res: print(r['H'],r['nA'],r['nB'],r['forest'],r['visits'])
    json.dump(res,open('splits%d.json'%h,'w'))
