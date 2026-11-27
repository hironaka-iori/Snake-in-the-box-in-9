"""Independent Q4 capacities from leaf elimination and subset maxima."""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import comb


@lru_cache(maxsize=1)
def capacities():
    n=1<<16
    adjacency=[sum(1<<(v^(1<<d)) for d in range(4)) for v in range(16)]
    classify=[bytearray(n) for _ in range(3)]
    even=sum(1<<v for v in range(16) if v.bit_count()%2==0)
    for mask in range(n):
        selected=[v for v in range(16) if mask>>v&1]
        degrees={v:(adjacency[v]&mask).bit_count() for v in selected}
        if any(deg>2 for deg in degrees.values()):continue
        leaves=[v for v in selected if degrees[v]<=1]
        rem=mask
        while leaves:
            v=leaves.pop()
            if not rem>>v&1:continue
            rem^=1<<v
            neighbours=adjacency[v]&rem
            if neighbours:
                assert neighbours.bit_count()==1
                w=neighbours.bit_length()-1
                degrees[w]-=1
                if degrees[w]<=1:leaves.append(w)
        if rem:continue
        vcount=len(selected)
        for table,w in zip(classify,(vcount,vcount+(mask&even).bit_count(),2*vcount-(mask&even).bit_count())):
            table[mask]=w
    for axis in range(16):
        bit=1<<axis
        for lo in range(0,n,2*bit):
            for index in range(lo,lo+bit):
                for table in classify:
                    if table[index]>table[index+bit]:table[index+bit]=table[index]
    h=sha256(bytes(x for triple in zip(*classify) for x in triple)).hexdigest()
    assert h=="58d3baf54c45b4e6b46558816c5a20e75eb256fe2dff4673e52aef52eafe3a1d"
    return classify[0]


def apply(q,selected,m):
    upper=set(m)
    table=capacities()
    for dimension in (3,4):
        for axes in combinations(range(8),dimension):
            coordinate_mask=sum(1<<i for i in axes)
            sub=sorted(sum(1<<axes[i] for i in range(dimension) if z>>i&1) for z in range(1<<dimension))
            for fixed in range(256):
                if fixed&coordinate_mask:continue
                sites=[fixed^x for x in sub]
                possible=sum(1<<i for i,v in enumerate(sites) if v in selected)
                occupied=sum(1<<(8+i) for i,v in enumerate(sites) if dimension==3 and v in upper)
                available=[selected[v] for v in sites if v in selected]
                cap=table[possible|occupied]-occupied.bit_count()
                assert cap>=0
                if cap>=len(available):continue
                if comb(len(available),cap+1)>64:
                    q.at_most(available,cap)
                else:
                    for c in combinations(available,cap+1):
                        q.clause([-x for x in c])
