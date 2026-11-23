"""Upper bound at fixed cross-layer ports by an adaptive partition into paired Q3 faces."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import gzip
import sys

def bits(x):
    while x:
        low = x & -x
        yield low.bit_length()-1
        x ^= low

def local_catalog():
    adj = [sum(1 << (x ^ (1 << j)) for j in range(4)) for x in range(16)]
    catalog = [[] for _ in range(256)]
    for mask in sorted(range(65536),key=int.bit_count,reverse=True):
        vs = list(bits(mask))
        degree = [(adj[x]&mask).bit_count() for x in vs]
        if max(degree, default=0)>2:
            continue
        todo = mask
        while todo:
            front = todo & -todo
            component = front
            while front:
                nxt = 0
                for x in bits(front):
                    nxt |= adj[x]
                front = nxt & mask & ~component
                component |= front
            if all((adj[x]&mask).bit_count()==2 for x in bits(component)):
                break
            todo &= ~component
        if todo:
            continue
        lo,hi=mask&255,mask>>8
        at_least_one=sum(1<<x for x,d in zip(vs,degree) if d>=1)
        at_least_two=sum(1<<x for x,d in zip(vs,degree) if d>=2)
        fold=lambda v:(v|(v>>8))&255
        catalog[lo&hi].append((len(vs),lo|hi,fold(at_least_one),fold(at_least_two)))
    return catalog

catalog = local_catalog()

@lru_cache(maxsize=250000)
def leaf(ports,e1,e2,e3):
    for size,used,d1,d2 in catalog[ports]:
        if not ((used&e3) or (d1&e2) or (d2&e1)):
            return size
    return -1024

@lru_cache(None)
def offsets(free):
    out=[0]
    for d in bits(free):
        out += [v|(1<<d) for v in out]
    return tuple(out)

def upper(P):
    @lru_cache(None)
    def visit(base,free):
        if free.bit_count()==3:
            p=a=b=c=0
            for i,z in enumerate(offsets(free)):
                v=base|z
                n=(neighbors[v] & (255^free)).bit_count()
                p |= (v in P)<<i
                a |= (n>=1)<<i
                b |= (n>=2)<<i
                c |= (n>=3)<<i
            return leaf(p,a,b,c)
        return min(visit(base,free^(1<<i))+visit(base|(1<<i),free^(1<<i)) for i in bits(free))
    neighbors=[sum(1<<i for i in range(8) if (v^(1<<i)) in P) for v in range(256)]
    return visit(0,255)-1

def ports(path,d):
    return frozenset((u% (1<<d)) | ((u>>(d+1))<<d) for u,v in zip(path,path[1:]) if (u^v)==1<<d)

if __name__ == "__main__":
    bank=Path(__file__).with_name("q9_port_followup_public191.txt.gz")
    with gzip.open(bank,"rt") as f:
        rows=[list(map(int,line.split())) for line in f]
    for r in map(int,sys.argv[1:] or [0]):
        path=rows[r]
        assert len(path)==len(set(path))==192 and all(0<=v<512 for v in path)
        assert all(((v^u).bit_count()==1)==(j+1==i) for i,v in enumerate(path) for j,u in enumerate(path[:i]))
        for d in range(9):
            P=ports(path,d)
            bound=upper(P)
            assert bound>=191
            print(r,d,len(P),bound,flush=True)
