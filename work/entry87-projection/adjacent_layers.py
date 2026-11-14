"""Freeze two adjacent layer sets in a 190-edge source and jointly rebuild the others."""
import argparse
from collections import Counter
from pathlib import Path
from joint_four_repair import sources
from layer_four import find
from solve import defects, save


def run(first,stop,radius,seconds,single=False):
    rows=[]
    prefix="one-fixed-layer" if single else "adjacent-layers"
    output=Path(f"{prefix}-{first}-{stop}-{radius}-{seconds}.json")
    for idx,(record,axes,q) in enumerate(sources()):
        if idx<first:continue
        if idx>=stop:break
        hint=[{v&127 for v in q if v>>7==layer} for layer in range(4)]
        sizes=[len(hint[layer]) for layer in (0,1,3,2)]
        choices=((0,),(1,),(3,),(2,)) if single else ((0,1),(1,3),(3,2),(2,0))
        for case,locked in enumerate(choices):
            if not rows:
                control=find(7,sizes,20,1,hint,0,True,191,locked)
                assert control["status"]=="FOUND" and not defects(control["witness"])
            decision=find(7,sizes,seconds,67+idx*4+case,hint,
                          radius if radius>=0 else None,True,193,locked)
            witness=decision.get("witness")
            if witness:
                assert len(witness)==193 and not defects(witness)
                assert all({v&127 for v in witness if v>>7==l}==hint[l] for l in locked)
            rows.append(dict(index=idx,source=record,axes=axes,fixed=locked,**decision))
            save(output,rows)
            if witness:return rows
    return rows


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("first",type=int);parser.add_argument("stop",type=int)
    parser.add_argument("--radius",type=int,default=-1);parser.add_argument("--seconds",type=int,default=20)
    parser.add_argument("--single",action="store_true")
    a=parser.parse_args();rows=run(a.first,a.stop,a.radius,a.seconds,a.single)
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
