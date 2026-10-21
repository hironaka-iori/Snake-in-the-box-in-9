# Hamiltonian quotient walks of Q4 (131 classes) + bank palette; interior pieces >= tmin; total >= T.
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys,time,json
from qmodel import QModel, check
from hamq import ham
from common import pc
A=set([0,1,2,5,6,13,24,26,27,28,29]); B=set([3,4,7,8,9,11,12,16,20,23,31]); M=set(range(32))-A-B
tmin=int(sys.argv[1]); T=int(sys.argv[2]); tl=float(sys.argv[3]); out=sys.argv[4]
walks=ham(4)
for wi,walk in enumerate(walks):
    m=len(walk)
    kw=dict(minsize={i:tmin for i in range(1,m-1)}, fix_start=False, target=T,
            allowed=[M|(A if pc(c)%2==0 else B) for c in walk], bnd_allowed=M)
    t=time.time(); Mo=QModel(5,4,list(walk),**kw); r,p=Mo.solve(tlimit=tl)
    rec=dict(walk=wi,cells=list(walk),tmin=tmin,target=T,result={None:'UNKNOWN',False:'UNSAT',True:'SAT'}[r],secs=round(time.time()-t,1),valid=check(p,9) if p else None)
    if p: rec['path']=p
    print(json.dumps({k:v for k,v in rec.items() if k not in('path','cells')}),flush=True)
    open(out,'a').write(json.dumps(rec)+'\n')
