from insertion import solve
from search import D,partition,validate
from collections import Counter
import json,random
p=json.loads((D.parent/'q9_explicit_q8_96_plus_94.json').read_text())['vertices']
assert validate(p) and len(p)==192
w=[(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
parts=[(ps,s) for s in range(9) for ps in partition(tuple(x for x in range(9) if x!=s))]
jobs=[(j,e) for j in range(len(parts)) for e in range(5)]
random.Random(43817).shuffle(jobs);counts=Counter()
for j,e in jobs:
    ps,s=parts[j];st,v,h,c=solve(w,ps,s,e,9000);counts[st]+=1
    print(json.dumps(dict(partition=j,group=e,status=st,conflicts=c,**({'found':v,'seam':h} if v else {}))),flush=True)
    if v:break
print(json.dumps(dict(done=True,counts=counts)),flush=True)
