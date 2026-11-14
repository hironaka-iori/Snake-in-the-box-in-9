"""Start from the actual opposite Q7 layers of every near-record four-layer snake and reoptimize the other two."""
import argparse,json,subprocess
from collections import Counter
from pathlib import Path
from joint_four_repair import sources
from zipper_native import solve_many
from zipper import arm
from solve import defects,save


def arrangements(q):
    paths=[[v&127 for v in q if v>>7==l] for l in (0,1,3,2)]
    for orientation in (False,True):
        p=paths if not orientation else [a[::-1] for a in paths[::-1]]
        yield p


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--nodes",type=int,default=5000000);p.add_argument("--seconds",type=float,default=0)
    a=p.parse_args();rows=[];best=0;bestq=None;file=Path(f"opposite-anchors-{a.nodes}-{a.seconds}.json")
    for idx,axes,q in sources():
        for orientation,(A,B0,C,D0) in enumerate(arrangements(q)):
            free=set(range(128))-(set(A)|set(C));ab=free|{A[-1],C[0]};ad=free|{C[-1]}
            assert set(B0)<=ab and set(D0)<=ad
            B,D=solve_many([(A[-1],C[0],ab),(C[-1],-1,ad)],a.nodes)
            if a.seconds:
                for ans,domain,root,end in ((B,ab,A[-1],C[0]),(D,ad,C[-1],None)):
                    if ans["complete"]:continue
                    r=arm(domain,root,end,a.seconds,23)
                    if len(r.get("path",[]))>ans["best"]:ans["q"]=r["path"];ans["best"]=len(r["path"])
                    if r.get("upper")==ans["best"]:ans["complete"]=True
            for ans,old in ((B,B0),(D,D0)):
                if ans["complete"]:assert ans["best"]>=len(old)
                if ans["best"]<len(old):ans["q"]=old;ans["best"]=len(old)
            hit=[*A,*[v|128 for v in B["q"]],*[v|384 for v in C],*[v|256 for v in D["q"]]]
            assert not defects(hit)
            if len(hit)-1>best:best=len(hit)-1;bestq=hit;print("best",idx,orientation,best,flush=True)
            rows.append(dict(index=idx,axes=axes,orientation=orientation,input_sizes=list(map(len,(A,B0,C,D0))),
                             left=A,third=C,middle=B,last=D,achieved_edges=len(hit)-1))
            save(file,dict(rows=rows,best_edges=best,best_path=bestq))
            if best>=192:break
        if best>=192:break
    print(len(rows),best,sum(r["middle"]["complete"] and r["last"]["complete"] for r in rows),flush=True)
