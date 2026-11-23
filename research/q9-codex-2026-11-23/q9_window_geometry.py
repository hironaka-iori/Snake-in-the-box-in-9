"""Lift overlapping canonical transition windows to one genuine cube path."""
import argparse
from collections import Counter
import json
from pathlib import Path


def canonical(sequence):
    names={}
    return tuple(names.setdefault(d,len(names)) for d in sequence)


def lift(windows,budget=100000,dimension=9):
    # Quotient once by permuting all coordinates, using the first complete window.
    if not windows:
        raise ValueError("need at least one window")
    visited=0
    exceeded=False
    def extend(word,vertices,level):
        nonlocal visited,exceeded
        if level==len(windows):
            return word
        if visited>=budget:
            exceeded=True
            return None
        visited+=1
        for direction in range(dimension):
            if canonical((*word[-8:],direction)) not in windows[level]:
                continue
            new=vertices[-1]^(1<<direction)
            if new in vertices or any((new^x).bit_count()==1 for x in vertices[:-1]):
                continue
            result=extend((*word,direction),(*vertices,new),level+1)
            if result is not None:
                return result
        return None

    for word in sorted(windows[0]):
        vertices=[0]
        for d in word:
            vertices.append(vertices[-1]^(1<<d))
        assert len(set(vertices))==10
        assert all(((v^w).bit_count()==1)==(i==j+1)
                   for i,v in enumerate(vertices) for j,w in enumerate(vertices[:i]))
        got=extend(word,tuple(vertices),1)
        if got is not None:
            return dict(status="LIFTED",word=got,nodes=visited)
    return dict(status="UNKNOWN" if exceeded else "EXHAUSTED",nodes=visited)


def scan(windows,maximum,budget):
    for width in range(2,min(maximum,len(windows))+1):
        seen={}
        for start in range(len(windows)-width+1):
            region=tuple(windows[start:start+width])
            seen.setdefault(region,[]).append(start)
        results=Counter()
        shortest=[]
        for region, locations in seen.items():
            row=lift(region,budget)
            results[row["status"]]+=1
            if row["status"]=="EXHAUSTED":
                shortest.append(dict(starts=locations,words=[sorted(x) for x in region],nodes=row["nodes"]))
        print(json.dumps(dict(steps=width+8,unique=len(seen),statuses=results,
                              impossible=shortest)),flush=True)
        if shortest:
            break


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("windows",type=Path)
    p.add_argument("--maximum",type=int,default=35)
    p.add_argument("--budget",type=int,default=100000)
    a=p.parse_args()
    windows=[frozenset(map(tuple,x)) for x in json.loads(a.windows.read_text())]
    scan(windows,a.maximum,a.budget)
