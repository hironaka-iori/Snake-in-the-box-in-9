from bank import *
from solver import solve
import sys
def partition(a):
    if not a:yield ();return
    for b in a[1:]:
        for tail in partition([x for x in a[1:] if x!=b]):yield ((a[0],b),)+tail
pp=[(ps,s) for s in range(9) for ps in partition([x for x in range(9) if x!=s])]
near=[list(map(int,l.split())) for l in (r/'q8_complete_single_cross_near_192.txt').read_text().splitlines()]
for p in near:
    assert len(p)==193 and len(set(p))==193 and sum((x^y).bit_count()==1 for j,y in enumerate(p) for x in p[:max(0,j-1)])==1
mode,limit,cap=map(int,sys.argv[1:]);rng=random.Random(41861+mode)
if mode==0:jobs=[(0,2,188,2,2,pi) for pi in range(len(pp))]
else:
    jobs=[]
    for idx,p in enumerate(near):
        for core,left,right in [(188,2,2),(189,1,2),(190,1,1),(191,2,2),(192,2,2),(188,3,4),(188,4,4)]:
            for off in range(193-core):
                for pi in rng.sample(range(len(pp)),30):jobs.append((idx,off,core,left,right,pi))
    rng.shuffle(jobs)
for idx,off,n,l,rh,pi in jobs[:limit]:
    w=trans(near[idx])[off:off+n];ps,s=pp[pi];st,p,k=solve(list(map(int,w)),ps,s,l,rh,cap)
    rec=dict(idx=idx,offset=off,w=w,left=l,right=rh,target=n+l+rh,group=pi,ps=ps,s=s,status=st,conflicts=k)
    if p:assert len(p)==n+l+rh+1 and valid(p);rec['path']=p
    print(json.dumps(rec,separators=(',',':')),flush=True)
    if p:break
