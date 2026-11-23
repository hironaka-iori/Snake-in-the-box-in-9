"""Create a reproducible bank of Q8 faces mutated independently at one or more vertices."""
import argparse
import random
from pathlib import Path
from itertools import combinations

def mutate(initial,rng,edits):
    s=set(initial)
    deg=[sum((u^(1<<d)) in s for d in range(8)) for u in range(256)]
    for j in range(edits):
        candidates=list(range(256));rng.shuffle(candidates)
        for u in candidates:
            nb=[u^(1<<d) for d in range(8)]
            if u in s:
                if deg[u]<1 or any(v in s and deg[v]<=1 for v in nb):continue
                s.remove(u);step=-1
            else:
                if not 1<=deg[u]<=2 or any(v in s and deg[v]>=2 for v in nb):continue
                s.add(u);step=1
            for v in nb:deg[v]+=step
            break
    return tuple(sorted(s))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('bank');ap.add_argument('salt',type=int);a=ap.parse_args()
    rng=random.Random(a.salt);seen=set();fresh=set()
    for l in Path(a.bank).read_text().splitlines():
        p=list(map(int,l.split()))
        for axis in range(9):
            mask=(1<<axis)-1
            for side in (0,1):
                s=tuple(sorted({(x&mask)|((x>>(axis+1))<<axis) for x in p if (x>>axis)&1==side}))
                if s in seen:continue
                seen.add(s)
                S=set(s);degrees=[sum((v^(1<<j)) in S for j in range(8)) for v in s]
                if max(degrees,default=0)>2 or degrees.count(0)>2 or not 6<=sum(d<2 for d in degrees)<=28:continue
                for edits in (1,1,2,3):
                    w=mutate(s,rng,edits)
                    if w!=s and w not in fresh:
                        fresh.add(w);print("F",*w)
