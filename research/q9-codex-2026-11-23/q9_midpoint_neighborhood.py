"""Partition midpoint cases by both adjoining edges, modulo the stabilizer."""
import argparse
from itertools import product
import json
from pathlib import Path

from q9_midpoint_reflection import representatives,run


def neighbors(distance,x,y):
    terminal=(1<<distance)-1
    types=[tuple(v>>d&1 for v in (terminal,x,y)) for d in range(9)]
    middle=x^y
    seen=set()
    for i,j in product(range(9),repeat=2):
        a,b=1<<i,1<<j
        if i==j or middle in (a,b):
            continue
        prev,succ=x^a,y^b
        if min(prev.bit_count(),distance_between(prev,terminal),
               succ.bit_count(),distance_between(succ,terminal))<2:
            continue
        signature=types[i],types[j]
        if signature in seen:
            continue
        seen.add(signature)
        yield prev,succ


def distance_between(a,b):
    return (a^b).bit_count()


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    p.add_argument("--distance",type=int,choices=(3,5,7,9))
    p.add_argument("--list",action="store_true")
    p.add_argument("--budget",type=int,default=90000)
    p.add_argument("--solver",choices=("cadical195","cadical300","glucose42"),default="cadical195")
    p.add_argument("--square-census",action="store_true")
    p.add_argument("--cycle-span",type=int,default=3)
    p.add_argument("--halves",action="store_true")
    a=p.parse_args()
    for d in ((a.distance,) if a.distance else (9,3,5,7)):
        for x,y in representatives(d):
            for a.outer in neighbors(d,x,y):
                print(json.dumps(dict(distance=d,edge=[x,y],outer=a.outer)
                                 if a.list else run(d,x,y,a)),flush=True)
