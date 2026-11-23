from bank import *
from solver import solve
import sys
rng=random.Random(843751);parts={}
def enum(ds):
    if not ds:yield ();return
    a=ds[0]
    for b in ds[1:]:
        for tail in enum([x for x in ds if x not in (a,b)]):yield ((a,b),)+tail
layouts=[(p,s) for s in range(9) for p in enum([x for x in range(9) if x!=s])]
sources={}
for n in [188,191,192]:
    for kind in ['aligned','registered']:
        rows=[line.split() for line in (d/f'{kind}{n}.txt').open()]
        unique={row[-1]:(int(row[0]),int(row[1]),row[-1]) for row in rows}
        sources[kind,n]=sorted(unique.values())[:24]
        assert sources[kind,n]
for t in range(1200):
    kind=['aligned','registered'][t%2];target=[192,195,196,192,192,195,196,192][(t//2)%8]
    n=188 if target==192 or t%16 in (2,3,4,5) else target-4
    count,job,w=rng.choice(sources[kind,n]);pi=rng.randrange(945);p,s=layouts[pi]
    l=(target-n)//2;h=target-n-l
    if rng.randrange(2):l,h=h,l
    st,path,k=solve(list(map(int,w)),p,s,l,h,5500)
    rec=dict(source=kind,job=job,common=count,w=w,ps=p,s=s,left=l,right=h,target=target,group=pi,status=st,conflicts=k)
    if path:assert valid(path) and len(path)==target+1;rec['path']=path
    print(json.dumps(rec,separators=(',',':')),flush=True)
    if path:break
