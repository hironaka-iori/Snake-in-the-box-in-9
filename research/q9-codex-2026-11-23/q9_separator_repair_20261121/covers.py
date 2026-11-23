import json,sys,random
from prepare import D,R,words,majority,NB
from solve import solve
jobs=list(map(json.loads,(D/'jobs.jsonl').read_text().splitlines()));rng=random.Random(69971);indices=list(range(len(jobs)));rng.shuffle(indices)
for i in indices[:int(sys.argv[1])]:
    c=jobs[i];A=majority(words[c['row']])
    for pieces in (2,3,4):
        st,cuts,conf,paths=solve(A,c,1100,pieces)
        if paths:
            print(json.dumps([i,pieces,sorted(set(v for p in paths for v in p if not v.bit_count()%2)),paths],separators=(',',':')),flush=True);break
