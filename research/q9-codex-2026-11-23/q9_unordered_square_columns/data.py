from pathlib import Path
from itertools import combinations
import json,gzip
D=Path(__file__).resolve().parent;R=D.parent
def canonical(p):
    w=[(a^b).bit_length() for a,b in zip(p,p[1:])]
    def fix(z):
        table={};return tuple(table.setdefault(c,len(table)) for c in z)
    return min(fix(w),fix(w[::-1]))
def check(p,dim=9):
    assert len(set(p))==len(p) and all(0<=v<1<<dim for v in p)
    assert all(((x^y).bit_count()==1)==(j+1==i) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
def permute(p,axes,dim=9):
    order=list(axes)+[i for i in range(dim) if i not in axes]
    return [sum(((v>>d)&1)<<j for j,d in enumerate(order)) for v in p]
def hist(p,dim=9):
    h=[0]*(1<<(dim-2))
    for v in p:h[v//4]+=1
    return h
def banks():
    with gzip.open(R/'q9_port_followup_public191.txt.gz','rt') as f:public=[list(map(int,l.split())) for l in f]
    near=[list(map(int,l.split()[2:])) for l in (R/'q9_via_q10/seven_donors.pts').open() if l.startswith('SEED')]
    arm={}
    for fn in ['join0.log','join1.log','closure_join0.log','closure_join1.log','outer.log']:
        for l in (R/'q9_gl_arm_join'/fn).open():
            s=l.split()
            if s[0]!='W':continue
            n=int(s[1 if fn=='outer.log' else 2]);p=list(map(int,s[-n-1:]))
            if n>=188:check(p);arm.setdefault(canonical(p),p)
    assert len(public)==131 and len(near)==7
    for p in public:check(p)
    for p in near:
        assert len(p)==len(set(p))==193
        assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
        assert sum((x^y).bit_count()==1 for j,y in enumerate(p) for x in p[:max(0,j-1)])==2
    return dict(near=near,public=public,arm=list(arm.values()))
if __name__=='__main__':
    b=banks();(D/'inputs.json').write_text(json.dumps(b));print({k:len(v) for k,v in b.items()})
