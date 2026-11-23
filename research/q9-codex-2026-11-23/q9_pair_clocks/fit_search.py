from ordered_end import solve
from search import D,validate
from collections import Counter
import random,json,sys
n,total,cap,seed=map(int,sys.argv[1:]);rows=(D/f'fits_{n}.txt').read_text().splitlines();rng=random.Random(seed);rng.shuffle(rows)
stats=Counter()
for job,row in enumerate(rows[:total]):
    q,layout,offset,start,length,changed,m,image=row.split();w=list(map(int,q));ds=list(map(int,layout));ps=[tuple(ds[j:j+2]) for j in range(0,8,2)];s=ds[-1];gr={d:i//2 for i,d in enumerate(ds)}
    start,offset,length=map(int,(start,offset,length))
    assert all(gr[int(image[int(m[offset+i])])] in [gr[w[2*(start+i)]],gr[w[2*(start+i)+1]]] for i in range(length))
    st,p,k=solve(w,ps,s,cap);stats[st]+=1
    if p:
        assert validate(p) and len(p)==n+1
        print(json.dumps(dict(found=p,q8=m,source_start=offset,target_start=start,length=length,map=image,groups=ps)),flush=True);break
    if job%25==24:print(json.dumps(dict(done_cases=job+1,counts=stats)),flush=True)
print(json.dumps(dict(done=True,counts=stats)),flush=True)
