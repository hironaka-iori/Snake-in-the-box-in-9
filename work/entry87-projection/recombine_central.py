"""Try all relative placements of rooted central runs and allow both free arms to change."""
import argparse
from collections import Counter
from itertools import combinations_with_replacement, permutations
import json
from pathlib import Path
import numpy as np
from three_central_runs import catalogue, outside_graph, decide
from three_cross_faces import normalize
from solve import save


def build(trim=0,reverse=False):
    bank={tuple(row["middle"]) for row in catalogue()}
    shapes=set()
    for pair in bank:
        for path in pair:
            for oriented in ((path,path[::-1]) if reverse else (path,)):
                for cut in range(trim+1):
                    run=oriented[:len(oriented)-cut]
                    assert len(run)>=2
                    shapes.add(normalize(run,run)[0])
    forms=sorted(shapes,key=lambda p:(len(p),p))
    axes=np.array(list(permutations(range(8))),dtype=np.uint8)
    table=np.zeros((len(axes),256),dtype=np.uint8)
    for v in range(1,256):
        k=(v&-v).bit_length()-1
        table[:,v]=table[:,v&(v-1)] | np.left_shift(1,axes[:,k])
    classes={};counts=Counter()
    for i,j in combinations_with_replacement(range(len(forms)),2):
        a,b=forms[i],forms[j]
        # A common crossing uses address zero. Each outer root must be outside
        # the closed neighbourhood of the central run on its own side.
        aset=set(a)
        blocked=aset|{v^(1<<k) for v in a for k in range(8)}
        avoid_root={a[-1]}|{a[-1]^(1<<k) for k in range(8)}
        reject_a=np.array([v in aset for v in range(256)],bool)
        reject_b=np.array([v in avoid_root for v in range(256)],bool)
        blocked_tip=np.array([v in blocked for v in range(256)],bool)
        eligible=~blocked_tip[table[:,b[-1]]]
        counts["indexed"]+=len(table)
        ids=np.flatnonzero(eligible)
        images=table[ids[:,None],np.array(b)[None,:]]
        good=~(np.any(reject_a[images[:,1:]],axis=1)|np.any(reject_b[images],axis=1))
        counts["compatible"]+=int(good.sum())
        # Multiple permutations can have the same effect on a path using
        # fewer than eight directions.
        for image in np.unique(images[good],axis=0):
            t=tuple(map(int,image));key=min(normalize(a,t),normalize(t,a))
            if key in classes:continue
            if key in bank:
                classes[key]=None;continue
            graphs=[outside_graph(key[s],key[1-s]) for s in (0,1)]
            available=len(set(graphs[0])|set(graphs[1]))
            needed=193-sum(map(len,key))
            classes[key]=dict(middle=key,forms=[i,j],available=available,needed=needed,
                              component_sizes=list(map(len,graphs)))
    assert all(k in classes for k in bank)
    rows=sorted((r for r in classes.values() if r is not None),
                key=lambda r:(r["needed"]-r["available"],r["middle"]))
    return dict(forms=forms,counts=dict(counts),known=len(bank),rows=rows)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--start",type=int,default=0);p.add_argument("--stop",type=int,default=0)
    p.add_argument("--budget",type=int,default=200000);p.add_argument("--target",type=int,choices=(192,193),default=193)
    p.add_argument("--checker",type=Path)
    p.add_argument("--trim",type=int,default=0);p.add_argument("--reverse",action="store_true")
    a=p.parse_args();suffix=f"-{a.trim}-{int(a.reverse)}" if a.trim or a.reverse else ""
    file=Path("recombined-central"+suffix+"-menu.json")
    if not a.stop:
        data=build(a.trim,a.reverse);save(file,data)
        print(len(data["forms"]),data["counts"],len(data["rows"]),
              sum(r["available"]>=r["needed"] for r in data["rows"]))
    else:
        data=json.loads(file.read_bytes())
        for i in range(a.start,min(a.stop,len(data["rows"]))):
            row=data["rows"][i]
            if row["available"]>=a.target-sum(map(len,row["middle"])):
                decide(row,f"mix{suffix}-{i}" if suffix else f"mix{i}",a.target,a.budget,a.checker.resolve() if a.checker else None)
