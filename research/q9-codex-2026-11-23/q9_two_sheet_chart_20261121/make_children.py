"""Grow an inverse 191 lift into bona fide ten-dimensional 196-edge mothers."""
from pathlib import Path
from collections import Counter
import json,random
from harvest import canon,valid
D=Path(__file__).resolve().parent
rng=random.Random(510484);seen=set();made=[]
for i,line in enumerate((D/'controls.pts').read_text().splitlines()):
    _,*raw=map(int,line.split());count=0
    for turn in range(5000):
        if count>=70:break
        l=rng.randrange(1,10);r=rng.randrange(1,10);p=raw[l:-r];s=set(p);muts=[]
        for j in rng.sample(range(1,len(p)-1),rng.randrange(3,18)):
            x=p[j-1]^p[j]^p[j+1];old=p[j];ns={x^1<<k for k in range(10)}
            if x not in s and ns&s-{old}=={p[j-1],p[j+1]}:s.remove(old);s.add(x);p[j]=x;muts.append(j+l)
        while len(p)<197:
            choices=[]
            for side,u in enumerate((p[0],p[-1])):
                for k in range(10):
                    x=u^1<<k
                    if x in s:continue
                    if any((x^(1<<d)) in s and (x^(1<<d))!=u for d in range(10)):continue
                    choices.append((side,x))
            if not choices:break
            side,x=rng.choice(choices);s.add(x)
            if side:p.append(x)
            else:p.insert(0,x)
        if len(p)<197:continue
        key=canon([(a^b).bit_length()-1 for a,b in zip(p,p[1:])])
        if key in seen:continue
        assert len(set(key))==10
        valid(p,10);seen.add(key);count+=1;made.append((p,dict(control=i,trim_left=l,trim_right=r,square_changes=muts)))
with (D/'children.pts').open('w') as f:
    for p,v in made:print(10,*p,file=f)
(D/'children.json').write_text(json.dumps([v for p,v in made],separators=(',',':'))+'\n')
print('shapes',len(made),'with_square_changes',sum(bool(v['square_changes']) for p,v in made),'unique_controls',len({v['control'] for _,v in made}))
