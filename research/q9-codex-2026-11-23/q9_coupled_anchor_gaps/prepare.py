from pathlib import Path
import json,itertools
out=Path(__file__).parent
root=out.parent
def defects(p):
    assert len(set(p))==len(p)
    assert all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
    return [(i,j) for i,a in enumerate(p) for j,b in enumerate(p[:i-1] if i else []) if (a^b).bit_count()==1]
def identity(p):
    ds=[(a^b).bit_length() for a,b in zip(p,p[1:])]
    def label(ds):
        d={};return tuple(d.setdefault(x,len(d)) for x in ds)
    return min(label(ds),label(reversed(ds)))
inputs=[]
for ln in (root/'q9_via_q10/seven_donors.pts').read_text().splitlines():
    t=ln.split()
    if t[0]=='SEED':
        p=list(map(int,t[2:])); c=defects(p)
        assert len(p)==193 and len(c)==2
        inputs.append((0,p))
seen=set()
for fn in sorted((root/'q9_even_arm_junction').glob('full_*.log')):
    for ln in fn.open():
        t=ln.split()
        if t[:2]==['W','191']:
            p=list(map(int,t[-192:]));assert len(p)==192 and not defects(p)
            key=identity(p)
            if key not in seen:
                inputs.append((1,p));seen.add(key)
with (out/'inputs.txt').open('w') as f:
    for i,(typ,p) in enumerate(inputs):print(typ,i,len(p),*p,file=f)
print('two-chord',sum(t==0 for t,p in inputs),'real191',len(seen))
