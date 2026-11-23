"""Enumerate all allowed subsets for sampled small releases, compare SAT."""
from collections import Counter
from itertools import combinations
import json
import random
from search import CUBE,HERE,N,check,release,search

rng=random.Random(721448)
bank=[list(map(int,line.split())) for line in open(HERE.parent/'q9_onechord_expanded_800.txt')]
stats=Counter()
tested=0
for p in rng.sample(bank,100):
    chord,=check(p)
    fixed=release(p,chord,rng.choice([4,6,8]),rng)
    deg={v:len(fixed.intersection(N[v])) for v in CUBE}
    free=sorted(v for v in CUBE-fixed if deg[v]<=2 and all(deg[w]<2 for w in fixed.intersection(N[v])))
    if len(free)>17:continue
    for target in (190,192):
        status,w=search(fixed,set(p),target,3000,CUBE)
        found=False
        for size in range(max(0,target+1-len(fixed)),len(free)+1):
            for group in combinations(free,size):
                tested+=1
                chosen=fixed.union(group)
                d={v:chosen.intersection(N[v]) for v in chosen}
                tips=[v for v,adj in d.items() if len(adj)==1]
                if len(tips)!=2 or any(len(adj) not in (1,2) for adj in d.values()):continue
                q=tips[:1]
                while len(q)<len(chosen):
                    cand=d[q[-1]]-set(q[-2:])
                    if len(cand)!=1:break
                    q.append(cand.pop())
                if len(q)==len(chosen):
                    assert not check(q)
                    found=True
                    break
            if found:break
        assert status==('FOUND' if found else 'UNSAT')
        if w:assert not check(w)
        stats[f'{target}_{status}']+=1
print(json.dumps(dict(checked=dict(stats),enumerated_subsets=tested)))
