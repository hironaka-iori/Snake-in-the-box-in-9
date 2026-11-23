import json,sys,random
from pathlib import Path
d=Path(__file__).resolve().parent
sys.path.insert(0,str(d.parent/'q9_free_upper_split_donors_20261121'))
from upper import solve
budget,n,goal=map(int,sys.argv[1:4]);solver=sys.argv[4]
cases=list(map(json.loads,(d/'cases.jsonl').read_text().splitlines()))
ids=list(range(len(cases)));rng=random.Random(532088);rng.shuffle(ids);ids.sort(key=lambda i:-len(cases[i]['w']))
for i in ids[:n]:
    c=cases[i];L=c['lo']+c['edge']
    for k in (3,2) if goal>=190 else (3,):
        status,rounds,conf,p=solve(L,goal,budget,(),k,solver)
        print(json.dumps(dict(case=i,cross=k,status=status,rounds=rounds,conflicts=conf,vertices=p),separators=(',',':')),flush=True)
        if p and len(p)>=193:sys.exit()
