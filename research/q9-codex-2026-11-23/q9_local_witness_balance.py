"""Relabel fresh coordinates without changing any local seventeen-step shape."""
import argparse
from collections import Counter
from functools import reduce
import json
from operator import xor
from pathlib import Path
from random import Random

from q9_window_geometry import canonical


def relabel(word,width,rng):
    counts=Counter()
    result=[]
    for i,c in enumerate(word):
        original=word[max(0,i-width+1):i]
        output=result[max(0,i-width+1):i]
        mapping=dict(zip(original,output))
        if c in mapping:
            label=mapping[c]
        else:
            unused=set(range(9)).difference(mapping.values())
            # Prefer underused dimensions while still generating distinct relabelings.
            label=min(sorted(unused),key=lambda d:counts[d]+rng.random()*5)
        counts[label]+=1
        result.append(label)
    freq=sorted(counts[i] for i in range(9))
    end=reduce(xor,(1<<d for d in result),0)
    return result,freq,end.bit_count()


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repair",type=Path)
    a=p.parse_args()
    row=next(x for x in map(json.loads,a.repair.read_text().splitlines()[1:])
             if x["status"]=="FEASIBLE_LOCAL_RELAXATION")
    word=list(map(int,row["word"]))
    width=row["width"]
    rng=Random(221)
    best=None
    for attempt in range(10000):
        seq,freq,distance=relabel(word,width,rng)
        if distance not in (3,5,7,9):
            continue
        if best is None or sum(freq[:2])>best["least_two"]:
            assert all(canonical(word[i:i+width])==canonical(seq[i:i+width])
                       for i in range(len(word)-width+1))
            best=dict(width=width,attempt=attempt+1,least_two=sum(freq[:2]),directions=freq,
                      distance=distance,word="".join(map(str,seq)))
        if sum(freq[:2])>=17:
            break
    print(json.dumps(best))
