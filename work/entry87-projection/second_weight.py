"""Classify all balanced lifts for the second weight of the Q9 reflexive cube code."""
from collections import Counter
from itertools import combinations
from pathlib import Path
from solve import save


def neighbours(v,n):
    return [v^(1<<j) for j in range(n)]


def mask(vertices):
    return sum(1<<v for v in vertices)


def solve(k):
    # The last two displayed coordinates are bits 8 and 9. At even residual
    # addresses pick 00 or 11; at odd addresses pick 01 or 10.
    centre=(1<<k)-1
    residual=sorted(neighbours(0,8)+neighbours(centre,8))
    assert len(set(residual))==16
    low=[v|((v.bit_count()%2)<<8) for v in residual]
    high=[v^768 for v in low]
    stars={v:mask(neighbours(v,10)) for v in range(1024)}
    flips=[stars[x]^stars[y] for x,y in zip(low,high)]
    words=[(1<<x)^(1<<y) for x,y in zip(low,high)]
    syndrome=0;u=mask(low)
    for x in low:syndrome^=stars[x]
    # Only pairs of opposite-parity-to-support centres at mutual distance
    # two have 16-site star differences. Include every such pair.
    pairs={}
    for v in range(1024):
        if v.bit_count()%2==0:continue
        for i,j in combinations(range(10),2):
            w=v^(1<<i)^(1<<j)
            if v<w:pairs[stars[v]^stars[w]]=(v,w)
    counts=Counter();examples=[]
    for step in range(1<<16):
        if step:
            bit=(step&-step).bit_length()-1
            syndrome^=flips[bit];u^=words[bit]
        if syndrome:continue
        counts["kernel"]+=1
        if u in pairs:counts["two_stars"]+=1
        else:examples.append([v for v in range(1024) if u>>v&1])
    return dict(centre_distance=k,lifts=1<<16,kernel=counts["kernel"],
                two_stars=counts["two_stars"],other_examples=examples)


if __name__=="__main__":
    rows=[solve(k) for k in (1,3,5,7)]
    save(Path("second-weight-lifts.json"),rows)
    for r in rows:print(r["centre_distance"],r["kernel"],r["two_stars"],len(r["other_examples"]))
