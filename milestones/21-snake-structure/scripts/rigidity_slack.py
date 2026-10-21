# Q9: bank quotient walk + palette; piece sizes >= bank size - slack; total >= target.
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys,time,json
from common import load,pc
from bankwalk import quotient
from palette import bank_palette
from qmodel import QModel, check
b=load()
idxs=[int(x) for x in sys.argv[1].split(',')]; tl=float(sys.argv[2]); slack=int(sys.argv[3]); T=int(sys.argv[4]); usepal=int(sys.argv[5]); out=sys.argv[6]
for idx in idxs:
    e=b[idx]; A,B,cell,hv=bank_palette(e); seq,sizes,L,H=quotient(e,4)
    M=set(range(32))-A-B
    kw=dict(minsize={i:max(1,s-slack) for i,s in enumerate(sizes)}, fix_start=False, target=T)
    if usepal: kw.update(allowed=[M|(A if pc(c)%2==0 else B) for c in seq], bnd_allowed=M)
    t=time.time(); Mo=QModel(5,4,seq,**kw); r,p=Mo.solve(tlimit=tl)
    rec=dict(idx=idx,visits=len(seq),palette=usepal,slack=slack,target=T,result={None:'UNKNOWN',False:'UNSAT',True:'SAT'}[r],secs=round(time.time()-t,1),cuts=Mo.cuts,
             valid=check(p,9) if p else None, length=len(p) if p else None)
    if p: rec['path']=p
    print(json.dumps({k:v for k,v in rec.items() if k!='path'}),flush=True)
    open(out,'a').write(json.dumps(rec)+'\n')
