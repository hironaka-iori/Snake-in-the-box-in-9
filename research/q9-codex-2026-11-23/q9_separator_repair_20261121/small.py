import json,random,sys
from prepare import D,majority,words,NB
from solve import solve
jobs=list(map(json.loads,(D/'jobs.jsonl').read_text().splitlines()))
rng=random.Random(69971);indices=list(range(len(jobs)));rng.shuffle(indices)
for i in indices:
    c=jobs[i]
    if c['k']!=5:continue
    k=max(1,len(c['remove']),len(c['added']));c={**c,'k':k}
    A=majority(words[c['row']]);st,n,conf,w=solve(A,c,1700)
    output=None
    if w:
        print(json.dumps([i,k,st,w]),flush=True);break
    for pc in (2,3,4,6):
        s,cut,conf,paths=solve(A,c,1100,pc)
        if paths:
            output=paths;break
    print(json.dumps([i,k,st,output],separators=(',',':')),flush=True)
