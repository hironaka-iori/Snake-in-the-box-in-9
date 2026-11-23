"""Independently verify and canonically deduplicate Q9 walks of 192 steps with one chord."""
import argparse
from collections import Counter
import json
from pathlib import Path


def check(p):
    assert len(p)==len(set(p))==193 and all(0<=x<512 for x in p)
    chords=[]
    for i,x in enumerate(p):
        for j in range(i+1,193):
            edge=(x^p[j]).bit_count()==1
            if j==i+1:assert edge
            elif edge:chords.append((i,j))
    assert len(chords)==1
    return chords[0]


def canonical(p):
    steps=[(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
    keys=[]
    for seq in (steps,steps[::-1]):
        coords={};keys.append(bytes(coords.setdefault(x,len(coords)) for x in seq))
    return min(keys)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources',nargs='+',type=Path)
    parser.add_argument('--out',type=Path)
    args=parser.parse_args();seen={};sources={};spans=Counter();internal=0
    for p in args.sources:
        inc=0
        for line in p.read_text().splitlines():
            w=list(map(int,line.split()));i,j=check(w);k=canonical(w)
            if k in seen:continue
            inc+=1;seen[k]=w;spans[j-i]+=1;internal+=(i>0 and j<192)
        sources[p.name]=inc
    if args.out:
        with args.out.open('w') as f:
            for w in seen.values():print(*w,file=f)
    print(json.dumps(dict(distinct=len(seen),internal_two_ends=internal,span_histogram=spans,added_by_source=sources)))
