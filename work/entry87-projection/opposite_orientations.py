"""Check every endpoint assignment on each of the two fixed opposite layer sets."""
import argparse
from pathlib import Path
from opposite_anchors import arrangements
from joint_four_repair import sources
from zipper_native import solve_many
from one_layer_core import parity_bound
from solve import defects,save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--nodes",type=int,default=10000000);a=p.parse_args();rows=[];univ=set(range(128))
    for i,(_,axes,q) in enumerate(sources()):
        if not a.first<=i<a.stop:continue
        for o,paths in enumerate(arrangements(q)):
            for flipA in (0,1):
                for flipC in (0,1):
                    A=paths[0][::-1] if flipA else paths[0];C=paths[2][::-1] if flipC else paths[2]
                    r=dict(source=i,opposite_pair=o,flip_first=flipA,flip_third=flipC)
                    if A[-1] in C or C[0] in A or C[-1] in A:r["status"]="endpoint collision"
                    elif not flipA and not flipC:r["status"]="source orientation certified"
                    else:
                        u=univ-set(A)-set(C);ab=u|{A[-1],C[0]};ad=u|{C[-1]}
                        cases=[(A[-1],C[0],ab),(C[-1],-1,ad)]
                        results=solve_many(cases,a.nodes);B,D=results
                        upper=[z["best"] if z["complete"] else parity_bound(domain,root,None if end==-1 else end)
                               for z,(root,end,domain) in zip(results,cases)]
                        low=len(A)+len(C)+B["best"]+D["best"]
                        r.update(status="EXHAUSTED" if sum(upper)+len(A)+len(C)<193 else "OPEN",
                                 upper=upper,arms=results,achieved_vertices=low)
                        if B["q"] and D["q"] and low>=193:
                            hit=A+[v|128 for v in B["q"]]+[v|384 for v in C]+[v|256 for v in D["q"]]
                            assert not defects(hit);r.update(status="FOUND",vertices=hit)
                    rows.append(r);save(Path(f"opposite-orientations-{a.first}-{a.stop}-{a.nodes}.json"),rows)
                    if r.get("vertices"):raise SystemExit(0)
