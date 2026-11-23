from bank import *
from solver import solve
rng=random.Random(135742)
def parts(ds):
    if not ds:yield ();return
    for c in ds[1:]:
        for tail in parts([x for x in ds if x not in (ds[0],c)]):yield ((ds[0],c),)+tail
ps=[(g,s) for s in range(9) for g in parts([x for x in range(9) if x!=s])]
old=set()
for line in (d/'public.jsonl').open():
    z=json.loads(line);old.add((z['w'],z['group'],z['left'],z['right']))
seeds=(r/'q9_gap_generations/prior191.words').read_text().split()
for i,word in enumerate(seeds):
    for n,goal,l,h in [(188,192,2,2),(191,195,2,2),(191,196,2,3)]:
        off=rng.randrange(192-n);w=word[off:off+n];pi=rng.randrange(945)
        while (w,pi,l,h) in old:pi=rng.randrange(945)
        old.add((w,pi,l,h));g,s=ps[pi];st,p,k=solve(list(map(int,w)),g,s,l,h,90000)
        rec=dict(idx=i,offset=off,w=w,group=pi,ps=g,s=s,left=l,right=h,target=goal,status=st,conflicts=k)
        if p:assert len(p)==goal+1 and valid(p);rec['path']=p
        print(json.dumps(rec,separators=(',',':')),flush=True)
        if p:raise SystemExit
