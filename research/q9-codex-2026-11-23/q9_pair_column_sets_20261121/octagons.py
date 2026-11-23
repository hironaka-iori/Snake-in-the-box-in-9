from functools import lru_cache
from itertools import combinations,permutations
@lru_cache(maxsize=None)
def cycles(axes):
    local=set()
    for r in range(16):
        for f in permutations([1,2,4,8]):
            x=r;word=[]
            for bit in f*2:word.append(x);x^=bit
            assert len(set(word))==8 and x==r
            local.add(tuple(sorted(word)))
    assert len(local)==24
    out=[]
    for dis in combinations(axes,4):
        shifts=[sum(1<<d for i,d in enumerate(dis) if b>>i&1) for b in range(16)]
        for base in range(512):
            if base&shifts[-1]:continue
            for P in local:out.append(tuple(-1-(base^shifts[q]) for q in P))
    return out
