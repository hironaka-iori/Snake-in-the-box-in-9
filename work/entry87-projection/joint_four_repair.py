"""Repair every four-layer 190-edge input jointly, allowing every layer size to vary."""
import argparse,json
from itertools import combinations
from pathlib import Path
from projection_seeds190 import seeds
from layer_four import find,normalized_hint
from solve import defects,save


def sources():
    for i,q in enumerate(seeds()):
        for a,b in combinations(range(9),2):
            layers=[(v>>a&1)|(v>>b&1)<<1 for v in q]
            cuts=[0]+[j for j in range(1,len(q)) if layers[j]!=layers[j-1]]
            if len(cuts)!=4 or len(set(layers))!=4:continue
            renamed={layers[j]:l for j,l in zip(cuts,(0,1,3,2))}
            keep=[k for k in range(9) if k not in (a,b)]
            full=[sum(((v>>k)&1)<<t for t,k in enumerate(keep))|(renamed[l]<<7) for v,l in zip(q,layers)]
            assert not defects(full)
            yield i,(a,b),full


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--radius",type=int,default=3);p.add_argument("--seconds",type=float,default=20)
    p.add_argument("--target",type=int,default=193);a=p.parse_args();rows=[]
    file=Path(f"joint-four-repair-{a.first}-{a.stop}-{a.radius}-{a.seconds}-{a.target}.json")
    for j,(i,axes,q) in enumerate(sources()):
        if j<a.first:continue
        if j>=a.stop:break
        h=normalized_hint(q);sizes=[len(h[t]) for t in (0,1,3,2)]
        if not rows:assert find(7,sizes,20,123,h,0,True,191)["status"]=="FOUND"
        r=find(7,sizes,a.seconds,97+37*j,h,a.radius,True,a.target)
        rows.append(dict(index=j,input=i,axes=axes,**r));save(file,rows)
        if r.get("witness"):break
    from collections import Counter
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
