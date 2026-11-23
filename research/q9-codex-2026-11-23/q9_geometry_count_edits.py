"""Test whether the 17-step obstruction survives one nearby count change."""
import argparse
import json
from pathlib import Path

from q9_window_geometry_dp import optimize,read_graph


def encode(x):
    value=0
    for d in x:
        value=6*value+d-1
    return value


def decode(x,width):
    return [x//6**i%6+1 for i in range(width-1,-1,-1)]


def updated_counts(old, position, value):
    digits=decode(old[0]//6,6)+[x%6+1 for x in old]
    assert [encode(digits[i:i+7]) for i in range(len(old))]==old
    digits[position+6]=value
    return [encode(digits[i:i+7]) for i in range(len(old))]


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("repo",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("--width",type=int,default=17)
    p.add_argument("--max-layer",type=int,default=50000)
    a=p.parse_args()
    graph=read_graph(a.repo)
    counts=graph[-1]
    forbidden=frozenset(tuple(map(tuple,k)) for k in json.loads(a.catalogue.read_text())["forbidden_triples"])
    for position in reversed(range(12,24)):
        old=counts[position]%6+1
        for delta in (1,-1,2,-2):
            value=old+delta
            if not 1<=value<=6:
                continue
            revised=updated_counts(counts,position,value)
            prefix=optimize(*graph[:-1],revised[:33],a.width,forbidden,a.max_layer)
            print(json.dumps(dict(position=position,old=old,value=value,phase="prefix",**prefix)),flush=True)
            if prefix["status"]!="FEASIBLE_LOCAL_RELAXATION":
                continue
            row=optimize(*graph[:-1],revised,a.width,forbidden,a.max_layer)
            print(json.dumps(dict(position=position,old=old,value=value,phase="full",**row)),flush=True)
            if row["status"]=="FEASIBLE_LOCAL_RELAXATION" and row["W6_corrected"]<373266:
                raise SystemExit(0)
