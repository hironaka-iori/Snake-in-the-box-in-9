"""Palette-restricted global model: Q9 = Q5(heavy) x Q4(light).
Even light cells may use only A u M, odd light cells only B u M."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, time, json
sys.path.insert(0,_os.path.join(REPO, 'milestones', '20-lower-bound-search', 'scripts'))
from lns2 import Model2
from common import *
from bankwalk import quotient
def bank_palette(e):
    vs=e['vertex_sequence']; seq,sizes,L,H=quotient(e,4)
    def cell(v): return sum(((v>>c)&1)<<i for i,c in enumerate(L))
    def hv(v): return sum(((v>>c)&1)<<i for i,c in enumerate(H))
    T={x:set() for x in range(32)}
    for v in vs: T[hv(v)].add(cell(v))
    A=set(x for x in range(32) if all(pc(c)%2==0 for c in T[x]) and T[x])
    B=set(x for x in range(32) if all(pc(c)%2==1 for c in T[x]) and T[x])
    return A,B,cell,hv
def forbidden(A,B,cell,hv):
    bad=[]
    for v in range(512):
        x=hv(v); c=cell(v)
        if (x in A and pc(c)%2==1) or (x in B and pc(c)%2==0): bad.append(v)
    return bad
if __name__=='__main__':
    idx=int(sys.argv[1]); T=int(sys.argv[2]); tl=float(sys.argv[3])
    e=load()[idx]
    A,B,cell,hv=bank_palette(e)
    bad=forbidden(A,B,cell,hv)
    t=time.time()
    M=Model2(set(),T,forbid=bad,solver='cadical195')
    r,p=M.run(time_budget=tl)
    print(idx,'free',len(M.free),'T',T,r,'cuts',M.cuts,'%.1fs'%(time.time()-t),flush=True)
