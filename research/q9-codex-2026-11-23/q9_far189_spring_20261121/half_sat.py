import json,sys
from pathlib import Path
from collections import Counter
from itertools import accumulate
from operator import xor
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R))
from search_q9_anchored_sets import search
from search_q9_wynn_plateau import canonical,verify
def p(w):return list(accumulate([1<<int(x) for x in w],xor,initial=0))
refs={k:{canonical(p(w)) for w in (D/f'comparison{k}.words').read_text().split()} for k in [190,191]};refs[192]=set()
counts=Counter();emitted=Counter()
for idx,l in enumerate((D/'half_survivors.log').open()):
    t=l.split()
    if t[0]!='HALF':continue
    f=set(map(int,t[3:]));assert len(f)==96
    a=next(iter(f));opp={v for v in range(512) if (v^a).bit_count()%2};domain=f|opp
    for k in [192,191,190]:
        while 1:
            st,w=search(f,f,k,100000,known=refs[k],allowed=domain)
            counts[k,st]+=1
            if not w:break
            assert verify(w) and len(w)==k+1 and f<=set(w)<=domain
            c=canonical(w);assert c not in refs[k];refs[k].add(c);emitted[k]+=1
            print(json.dumps(dict(case=idx,goal=k,vertices=w,word=''.join(map(str,c)))),flush=True)
            if k==192:sys.exit()
print(json.dumps(dict(done=True,states={str(k):v for k,v in counts.items()},novel=emitted)),flush=True)
