from monotone_sat import check,search,here
from collections import Counter
from itertools import chain
import random,json
bank={};rng=random.Random(93191)
for row in (here/'seven_donors.pts').read_text().splitlines():
    kind,i,*data=row.split(); i=int(i); ns=list(map(int,data))
    if kind=='SEED':bank[i]=(ns,[])
    else:bank[i][1].append(set(ns[1:]))
def emit(data):print(json.dumps(data,separators=(',',':')),flush=True)
for i,(p,donors) in bank.items():
    ref=set(p); assert len(check(p))==2 and len(donors)==400
    donor=donors[0]; adj={x:[v for d in range(9) if (v:=x^1<<d) in donor] for x in donor}; q=[next(x for x,nb in adj.items() if len(nb)==1)]
    marked=set(q)
    for _ in range(191):
        add=[v for v in adj[q[-1]] if v not in marked];assert len(add)==1
        q+=add;marked.update(add)
    assert len(marked)==192 and not check(q)
    st,v=search(ref&donor,donor,191,5000,ref|donor)
    assert v and len(v)>=192 and not check(v)
    emit(dict(control=i,status=st,edges=len(v)-1))
stats=Counter();seen=set()
for phase in range(60):
    for i,(p,donors) in bank.items():
        base=set(p);d=2+(phase%7);sub=rng.sample(donors[:min(400,16*(1+phase))],d)
        pool=set.union(base,*sub);core=set.intersection(base,*sub)
        if phase%3==0:
            c=check(p);vs={p[j] for pair in c for j in pair}
            pool.update(x for x in range(512) if min((x^v).bit_count() for v in vs)<=2)
        if phase%4==1:core=set(rng.sample(sorted(core),max(1,len(core)//2)))
        if phase%4==2:core={next(iter(core))} if core else {p[0]}
        if not core:core={p[0]}
        k=(frozenset(core),frozenset(pool))
        if k in seen:continue
        seen.add(k);st,v=search(core,sub[0],192,16000,pool);stats[st]+=1
        if v:assert len(v)>=193 and not check(v)
        emit(dict(seed=i,phase=phase,pool=len(pool),fixed=len(core),status=st,witness=v))
        if v:raise SystemExit
emit(dict(done=True,counts=stats))
