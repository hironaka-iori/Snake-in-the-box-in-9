from buckets import run
from search import D,axes,validate
import json,random
from collections import Counter
words=[list(map(int,w)) for w in (D.parent/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==192]
bank=[]
for w in words:
    p=axes(w)
    if sum((x^y).bit_count()==1 for j,y in enumerate(p) for x in p[:max(j-1,0)])==2:bank.append(w)
rows=[json.loads(l) for l in (D/'two.jsonl').read_text().splitlines()]
pending=[d for d in rows if d.get('status')=='UNKNOWN'];assert len(pending)==526
rng=random.Random(84711);rng.shuffle(pending);stats=Counter()
for x in pending:
    groups=[*map(tuple,x['pairs']),(x['single'],)];st,p,k=run(bank[x['row']],groups,90000);stats[st]+=1
    print(json.dumps(dict(row=x['row'],partition=x['partition'],status=st,conflicts=k,**({'path':p} if p else {}))),flush=True)
    if p:assert validate(p);break
print(json.dumps(dict(done=True,counts=stats)),flush=True)
