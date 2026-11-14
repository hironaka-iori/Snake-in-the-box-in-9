"""Join all realizable one-anchor changes on each face, preserving either length split."""
import argparse
from collections import Counter
from itertools import product
from pathlib import Path
from joint_parity import orders,representatives,assemble
from paired_seeds import extract
from solve import defects,save


def changes(anchors,cap):
    for x in sorted(anchors-{0}):
        for y in range(256):
            if y.bit_count()%2 or y in anchors:continue
            edited=tuple(sorted((anchors-{x})|{y}))
            found=orders(edited,cap)
            if found:yield set(edited),[x,y],found


def run(a):
    rows=[]
    for i,source in enumerate(extract()):
        if not a.start<=i<a.stop:continue
        A=set(source["parent"][::2]);B=set(source["known_partner"][::2])
        for cap in (0,1):
            left=list(changes(A,cap==0));right=list(changes(B,cap==1))
            counts=Counter();report=dict(index=i,odd_end=cap,orderable=[len(left),len(right)])
            for (aa,ea,oa),(bb,eb,ob) in product(left,right):
                if aa&bb!={0}:continue
                counts["nonoverlapping anchor pairs"]+=1
                for (xa,wa),(xb,wb) in product(oa,ob):
                    counts["order pairs"]+=1
                    reps=representatives(wa+wb)
                    if reps is None:continue
                    q=assemble(xa,reps[:len(wa)])[::-1]+[v^256 for v in assemble(xb,reps[len(wa):])]
                    assert len(q)==193 and not defects(q)
                    report.update(witness=q,edits=[ea,eb]);break
                if "witness" in report:break
            report["counts"]=counts;rows.append(report)
            if "witness" in report:break
        if "witness" in rows[-1]:break
    save(Path(f"joint-distributed-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum((Counter(r["counts"]) for r in rows),Counter()),
          sum("witness" in r for r in rows),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    run(p.parse_args())
