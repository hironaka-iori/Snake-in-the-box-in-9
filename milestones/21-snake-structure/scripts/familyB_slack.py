# Family B (entries 127-130): Q6 heavy x Q3 light, own palette, sizes >= bank - slack, total >= T
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import sys,time,json
from common import load,pc
from bankwalk import quotient
from qmodel import QModel, check
b=load()
idxs=[int(x) for x in sys.argv[1].split(',')]; tl=float(sys.argv[2]); slack=int(sys.argv[3]); T=int(sys.argv[4]); usepal=int(sys.argv[5]); out=sys.argv[6]
for idx in idxs:
    e=b[idx]; seq,sizes,L,H=quotient(e,3); vs=e['vertex_sequence']
    def cell(v): return sum(((v>>c)&1)<<i for i,c in enumerate(L))
    def hv(v): return sum(((v>>c)&1)<<i for i,c in enumerate(H))
    Tm={x:set() for x in range(64)}
    for v in vs: Tm[hv(v)].add(cell(v))
    A=set(x for x in Tm if Tm[x] and all(pc(c)%2==0 for c in Tm[x])); B=set(x for x in Tm if Tm[x] and all(pc(c)%2==1 for c in Tm[x]))
    M=set(range(64))-A-B
    kw=dict(minsize={i:max(1,s-slack) for i,s in enumerate(sizes)}, fix_start=False, target=T)
    if usepal: kw.update(allowed=[M|(A if pc(c)%2==0 else B) for c in seq], bnd_allowed=M)
    t=time.time(); Mo=QModel(6,3,seq,**kw); r,p=Mo.solve(tlimit=tl)
    rec=dict(idx=idx,visits=len(seq),palette=usepal,palette_sizes=[len(A),len(B),len(M)],slack=slack,target=T,result={None:'UNKNOWN',False:'UNSAT',True:'SAT'}[r],secs=round(time.time()-t,1),valid=check(p,9) if p else None,length=len(p) if p else None)
    print(json.dumps(rec),flush=True); open(out,'a').write(json.dumps(rec)+'\n')
