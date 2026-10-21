import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
from common import *
def quotient(e, k):
    vs=e['vertex_sequence']; L=light(e,k); H=[c for c in range(9) if c not in L]
    def cell(v): return sum(((v>>c)&1)<<i for i,c in enumerate(L))
    def hv(v): return sum(((v>>c)&1)<<i for i,c in enumerate(H))
    seq=[];sizes=[]
    for v in vs:
        c=cell(v)
        if not seq or seq[-1]!=c: seq.append(c); sizes.append(0)
        sizes[-1]+=1
    return seq,sizes,L,H
