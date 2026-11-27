"""Independently compute Q4 forest capacities and compare every native table entry."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json

def validate(native,dest):
    near=[sum(1<<(v^(1<<i)) for i in range(4)) for v in range(16)]
    evens=sum(1<<v for v in range(16) if v.bit_count()%2==0)
    n=1<<16
    values=[bytearray(n) for _ in range(3)]
    histogram=Counter()
    for s in range(n):
        degrees=[(near[v]&s).bit_count() for v in range(16) if s>>v&1]
        if any(deg>2 for deg in degrees):continue
        waiting=s;components=0
        while waiting:
            todo=waiting&-waiting;waiting^=todo;components+=1
            while todo:
                v=todo&-todo;todo^=v
                add=near[v.bit_length()-1]&waiting
                waiting^=add;todo|=add
        size=len(degrees)
        if sum(degrees)!=2*(size-components):continue
        e=(evens&s).bit_count()
        for array,value in zip(values,(size,size+e,2*size-e)):array[s]=value
        histogram[size]+=1
    for v in range(16):
        bit=1<<v
        for offset in range(bit,n,2*bit):
            for s in range(offset,offset+bit):
                for arr in values:
                    if arr[s^bit]>arr[s]:arr[s]=arr[s^bit]
    literal=bytes(x for triple in zip(*values) for x in triple)
    assert native==literal
    record=dict(available_masks=n,matched_weighted_capacities=3*n,weights=[[1,1],[2,1],[1,2]],
                linear_forests_by_vertices=dict(sorted(histogram.items())),full_q4_capacities=[a[-1] for a in values],
                sha256=sha256(literal).hexdigest(),q7_faces=[list(range(16*i,16*(i+1))) for i in range(8)])
    dest.write_text(json.dumps(record,indent=2)+"\n",encoding="utf8",newline="\n")
