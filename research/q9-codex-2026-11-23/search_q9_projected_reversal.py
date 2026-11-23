"""Exchange two nonconsecutive projected edges and reverse the intervening walk."""
import argparse
import json
import random
from collections import defaultdict
from pathlib import Path
from search_q9_square_fiber_lift import lift, projections
from search_q9_flexible_corners import solve
from search_q9_two_flexible_ends import verify


def normalized(p):
    bits={}
    q=bytearray([0])
    for a,b in zip(p,p[1:]):
        edge=a^b
        assert edge.bit_count()==1
        q.append(q[-1]^(1<<bits.setdefault(edge,len(bits))))
    return bytes(q)


def family(bank_path, limit):
    bases=set()
    for line in Path(bank_path).read_text().splitlines():
        v=list(map(int,line.split()))
        verify(v,191)
        seq=[(a^b).bit_length()-1 for a,b in zip(v,v[1:])]
        for p,h in projections(seq): bases.add(min(normalized(p),normalized(p[::-1])))
    seen=set(bases)
    keys=sorted(bases)
    rng=random.Random(261120)
    rng.shuffle(keys)
    for p in keys:
        visits=defaultdict(list)
        for j,v in enumerate(p[:-1]):visits[v].append(j)
        candidates=[]
        for i,(a,b) in enumerate(zip(p,p[1:])):
            for d in range(7):
                c=a^(1<<d)
                for j in visits[c]:
                    if j-i < 8 or (b^p[j+1]).bit_count()!=1:continue
                    if len({a,b,c,p[j+1]})!=4:continue
                    candidates.append((i,j))
        rng.shuffle(candidates)
        for i,j in candidates[:18]:
            q=p[:i+1]+p[i+1:j+1][::-1]+p[j+1:]
            key=min(normalized(q),normalized(q[::-1]))
            if key in seen:continue
            seen.add(key)
            yield key,p,i,j
            if len(seen)-len(bases)>=limit:return


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bank",default="/tmp/q9_core_191bank_m19.txt")
    ap.add_argument("--limit",default=5000,type=int)
    args=ap.parse_args()
    for q,p,i,j in family(args.bank,args.limit):
        # The key was normalized in either direction. Cover all odd interior sites.
        ids=list(range(1,len(q)-1,2))
        st,w=solve(q,[],ids,192,2200,True)
        if w:verify(w,192)
        print(json.dumps([st,p.hex(),i,j,q.hex(),w],separators=(",",":")),flush=True)
        if w:break
