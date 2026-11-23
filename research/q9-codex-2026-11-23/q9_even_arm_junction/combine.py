from bank import D,canon
from collections import Counter
import json,random
def occupied(ms):
    p=[0]
    for m in ms:p.append(p[-1]^m)
    return p
root=[tuple(map(int,l.split())) for l in (D/'arms.txt').read_text().splitlines()];ids={v:i for i,v in enumerate(root)};origin={};witnesses=[]
for ln in (D/'alternate_source.txt').read_text().splitlines():
    i,*a=map(int,ln.split());x=occupied(root[i]);y=occupied(a);assert len(x)==len(y)==49 and set(x)==set(y) and y!=x
    cnt=Counter(v^(1<<d) for v in x for d in range(9))
    for u,v in zip(y,y[1:]):
        m=u^v;assert m.bit_count()==2 and any(cnt[z]==2 for z in (u^(m&-m),v^(m&-m)))
    k=canon(a);j=ids.setdefault(k,len(ids));origin.setdefault(j,i)
new=list(range(len(root),len(ids)));random.Random(844071).shuffle(new);orig=list(map(int,(D/'order.txt').read_text().split()));order=new+orig
(D/'combined_arms.txt').write_text(''.join(' '.join(map(str,k))+'\n' for k in ids))
(D/'combined_order.txt').write_text(''.join(str(i)+'\n' for i in order))
(D/'alternate_provenance.json').write_text(json.dumps(origin,separators=(',',':')))
print(len(root),len(new),len(ids),len(new)*len(root)+len(new)*(len(new)+1)//2)
