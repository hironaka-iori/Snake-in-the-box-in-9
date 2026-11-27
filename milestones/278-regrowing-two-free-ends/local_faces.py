"""Necessary constraints from four-cubes, including the four-cubes that meet both faces."""
from functools import lru_cache
from hashlib import sha256
from itertools import combinations
from math import comb

@lru_cache(maxsize=1)
def capacities():
    near=[sum(1<<(v^(1<<i)) for i in range(4)) for v in range(16)]
    evens=sum(1<<v for v in range(16) if v.bit_count()%2==0)
    weights=[bytearray(65536) for _ in range(3)]
    for mask in range(65536):
        rest=mask;degree_total=0;components=0
        while rest:
            todo=rest&-rest;rest^=todo;components+=1
            while todo:
                x=todo&-todo;todo^=x
                neighbors=near[x.bit_length()-1]&mask
                if neighbors.bit_count()>2:break
                degree_total+=neighbors.bit_count()
                add=neighbors&rest;rest^=add;todo|=add
            else:continue
            break
        else:
            size=mask.bit_count();even=(mask&evens).bit_count()
            if degree_total==2*(size-components):
                weights[0][mask]=size;weights[1][mask]=size+even;weights[2][mask]=2*size-even
    for mask in range(1,65536):
        bits=mask
        while bits:
            b=bits&-bits;bits^=b
            for arr in weights:
                if arr[mask^b]>arr[mask]:arr[mask]=arr[mask^b]
    data=bytes(x for triple in zip(*weights) for x in triple)
    assert sha256(data).hexdigest()=="58d3baf54c45b4e6b46558816c5a20e75eb256fe2dff4673e52aef52eafe3a1d"
    return weights[0]

@lru_cache(maxsize=2)
def slices(d):
    cubes=[]
    for axes in combinations(range(8),d):
        offsets=[0]
        for j in axes:offsets+= [v|(1<<j) for v in offsets]
        for start in range(256):
            if not start&offsets[-1]:cubes.append([start|v for v in offsets])
    return cubes

def add(cnf,chosen,m):
    table=capacities();upper=set(m)
    for d in (3,4):
        for sites in slices(d):
            literals=[chosen[v] for v in sites if v in chosen]
            lower_mask=sum(1<<i for i,v in enumerate(sites) if v in chosen)
            upper_mask=sum(1<<(8+i) for i,v in enumerate(sites) if v in upper) if d==3 else 0
            lim=table[lower_mask|upper_mask]-upper_mask.bit_count()
            if lim>=len(literals):continue
            assert lim>=0
            if comb(len(literals),lim+1)<=64:
                for group in combinations(literals,lim+1):cnf.clauses.append([-x for x in group])
            else:
                cnf.at_most(literals,lim)

