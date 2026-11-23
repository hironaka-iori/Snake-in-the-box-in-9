from itertools import product
from collections import Counter
from monotone_sat import check,here,search
import json,random
bank=[]
for w in (here/'monotone_near.words').read_text().split():
    if len(w)!=192:continue
    p=[0]
    for c in w:p.append(p[-1]^(1<<int(c)))
    cs=check(p)
    if len(cs)==2:bank.append((w,p,cs))
assert len(bank)==7
seen=set();counter=Counter()
for rad,padr,flanks in [(3,0,6),(3,2,9),(4,0,7),(3,3,9),(4,2,12),(4,3,14)]:
    for k,(word,p,chords) in enumerate(bank):
        for side in product([0,1],repeat=2):
            centers=[c[t] for c,t in zip(chords,side)]
            fixed={p[j] for j in range(len(p)) if all((p[j]^p[c]).bit_count()>rad and abs(j-c)>flanks for c in centers) and min((p[j]^p[0]).bit_count(),(p[j]^p[-1]).bit_count())>padr}
            key=frozenset(fixed)
            if not key or key in seen:continue
            seen.add(key)
            status,v=search(fixed,set(p),192,30000,set(range(512)));counter[status]+=1
            if v:assert len(v)>=193 and not check(v)
            print(json.dumps(dict(seed=k,dirs=side,radius=rad,end_radius=padr,flanks=flanks,fixed=len(fixed),status=status,witness=v)),flush=True)
            if v:raise SystemExit
print(json.dumps(dict(done=True,counts=counter)),flush=True)
