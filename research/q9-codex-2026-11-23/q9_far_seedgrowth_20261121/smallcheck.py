from collections import Counter
from itertools import groupby
from pathlib import Path
import random,subprocess,json
from prepare import D,R,NB
rng=random.Random(2043)
def brute(q,h,e,goal):
    s=set(q)
    def visit(l,r,c,left):
        if len(s)==goal+1:return True
        if left and visit(l,r,c,False):return True
        tip=l if left else r
        for v in NB[tip]-s:
            cost=c+(v not in h)
            if cost>e or len(NB[v]&s)!=1:continue
            s.add(v)
            if visit(v if left else l,r if left else v,cost,left):return True
            s.remove(v)
        return False
    return visit(q[0],q[-1],len(s-h),True)
jobs=[]
for i in range(165):
    p=[rng.randrange(16)]
    while len(p)<4:
        xs=[x for x in NB[p[-1]]-set(p) if x<16 and len(NB[x]&set(p))==1]
        if not xs:break
        p.append(rng.choice(sorted(xs)))
    h=set(p)|set(rng.sample(range(16),rng.randrange(3,13)))
    e=rng.randrange(0,3);target=rng.randrange(5,10)
    jobs.append((target,p,h,e))
res=Counter();total=0
for goal,g in groupby(sorted(jobs,key=lambda a:a[0]),key=lambda a:a[0]):
    group=list(g);data=''.join(' '.join(map(str,[i,e,1000000,4,len(h),*sorted(h),len(q),*q]))+'\n' for i,(_,q,h,e) in enumerate(group))
    out=subprocess.check_output(['/tmp/q9_far_grow21',str(goal),'1'],input=data,text=True)
    records=[list(map(int,t[1:])) for l in out.splitlines() if (t:=l.split())[0]=='ROW']
    assert len(records)==len(group)
    for r,(_,q,h,e) in zip(records,group):
        exact=brute(q,h,e,goal);assert not r[5] and bool(r[8])==exact
        res[str(exact)]+=1;total+=1
print(json.dumps(dict(independent_inputs=total,results=res)))
