from data import *
from model import solve
from random import Random
import sys
family,total,seed,budget=sys.argv[1:];total=int(total);budget=int(budget);rng=Random(int(seed));db=json.loads((D/'inputs.json').read_text())
axes=list(combinations(range(9),2));source=family.split('_')[0];bank=db[source];sweep=[(j,a) for j in range(len(bank)) for a in axes];rng.shuffle(sweep)
if family in ('public_sample','arm_sample'):
    sweep=[(j,rng.choice(axes)) for j in range(len(bank))];rng.shuffle(sweep)
for t in range(total):
    j,ab=sweep[t%len(sweep)];p=permute(bank[j],ab);h=hist(p);defects=[(x,y) for i,y in enumerate(p) for x in p[:max(i-1,0)] if (x^y).bit_count()==1]
    style=family.split('_')[1];target=192;loss=0;dn=up=None
    if style in ('mixed','transfer'):
        target=192 if style=='transfer' or t%4==0 else 195+(t%3==0)
        loss=1+(t%5==0)
    elif style=='higher':target=(195,196)[t%2];loss=t%3==0
    elif style=='sample' and t>=len(bank):target=(192,195,196)[(t//len(bank))%3];loss=t%7==5
    if style=='transfer' and t%3:
        # Changes near a chord are preferred, but independent distant columns remain eligible.
        centers=list({v//4 for pair in defects for v in pair}) or [p[0]//4,p[-1]//4]
        allowed=set(centers)
        for v in centers:allowed.update(v^1<<a for a in range(7))
        allowed.update(rng.sample(range(128),12 if t%3==1 else 24));up=allowed;dn=allowed
    z=solve(h,target,int(loss),dn,up,hint=p,budget=budget)
    if 'path' in z:check(z['path'])
    record=dict(source=source,id=j,axes=ab,target=target,loss=int(loss),down=sorted(dn) if dn is not None else None,up=sorted(up) if up is not None else None,**z)
    print(json.dumps(record,separators=(',',':')),flush=True)
    if z['status']=='FOUND':raise SystemExit
