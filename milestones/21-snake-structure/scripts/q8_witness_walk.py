# Q8 sanity: witness quotient walk (Q5 x Q3), sizes >= witness sizes, (a) no growth -> SAT, (b) growth -> must be UNSAT since a(8)=98
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)
import json,time,sys
from qmodel import QModel, check
from collections import Counter
w=json.load(open(_os.path.join(REPO, 'outputs', 'snake8_witness.json')))
vs=w['vertex_sequence']; cc=Counter((a^b).bit_length()-1 for a,b in zip(vs,vs[1:]))
k=int(sys.argv[1]); order=sorted(range(8),key=lambda c:cc[c]); L=order[:k]
def cell(v): return sum(((v>>c)&1)<<i for i,c in enumerate(L))
seq=[];sizes=[]
for v in vs:
    c=cell(v)
    if not seq or seq[-1]!=c: seq.append(c); sizes.append(0)
    sizes[-1]+=1
print('walk',seq,'sizes',sizes)
for mode in ('control','grow'):
    t=time.time()
    kw=dict(minsize={i:s for i,s in enumerate(sizes)}, fix_start=False)
    if mode=='grow': kw['grow']={i:s for i,s in enumerate(sizes)}
    M=QModel(8-k,k,seq,**kw)
    r,p=M.solve(tlimit=float(sys.argv[2]))
    print(mode,r,'%.1fs'%(time.time()-t),'len',len(p) if p else None,'valid',check(p,8) if p else None,flush=True)
