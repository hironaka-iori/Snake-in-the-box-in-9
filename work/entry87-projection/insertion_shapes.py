"""Exact interval-graph obstructions for the whole one-insertion family."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
from solve import paths,save

SHAPES=(1<<2,1<<3,(1<<0)|(1<<1),(1<<0)|(1<<7),(1<<1)|(1<<6))
# Retained coordinate masks are densely packed in increasing coordinate order.
# For {0,1,4}, the integer addresses 19 and 18 become 7 and 6.


def automorphisms():
    from itertools import permutations
    images=[]
    for perm in permutations(range(3)):
        for delta in range(8):
            pi=[sum(((x>>k)&1)<<new for k,new in enumerate(perm))^delta for x in range(8)]
            out=[]
            for shape in SHAPES:
                out.append(sum(1<<pi[x] for x in range(8) if shape>>x&1))
            images.append(tuple(sorted(out)))
    return sorted(set(images))


def projected_intervals(q,keep):
    def packed(x):
        return sum(((x>>c)&1)<<j for j,c in enumerate(keep))
    z=[packed(x) for x in q]
    intervals=[0]
    for i,x in enumerate(z):
        if i and x==z[i-1]:
            intervals.append(0)
        intervals[-1]|=1<<x
    return intervals


def patterns():
    families=automorphisms()
    lookup=[sum(1<<g for g,fam in enumerate(families) if any(s&t==s for s in fam))
            for t in range(256)]
    return families,lookup


def scores(tr,families,lookup):
    hist=[Counter(tr[p::2]) for p in (0,1)]
    out=[]
    for p in range(2):
        ranked=[0]*len(families)
        for t,m in hist[p].items():
            options=lookup[t]
            while options:
                low=options&-options
                ranked[low.bit_length()-1]+=m
                options-=low
        value=max(ranked)
        out.append((value,ranked.index(value)))
    return out


if __name__=="__main__":
    p,q=paths()
    families,lookup=patterns()
    result=[]
    for keep in combinations(range(9),3):
        tr=projected_intervals(q,keep)
        result.append(dict(retained=keep,values=scores(tr,families,lookup)))
    print("orbits",len(families),"target excluded",[(x["retained"],x["values"]) for x in result if max(r[0] for r in x["values"])>32])
    save(Path("shape-orbit-scores.json"),dict(families=families,cases=result))
