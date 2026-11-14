"""Exhaust two free neighbouring layers with their shared crossing completely movable."""
import argparse
from collections import Counter
from pathlib import Path
import subprocess
from joint_four_repair import sources
from opposite_anchors import arrangements
from solve import defects,save


def run(i,paths,target,budget,mode="prefix",flips=(0,0)):
    if mode=="outer":
        first=paths[0][-1 if flips[0] else 0]
        last=paths[3][0 if flips[1] else -1]
        if ((first^last).bit_count()+1)%2!=(target-1)%2:
            return dict(status="ENDPOINT PARITY",third_nodes=0,last_nodes=0,last_calls=0,vertices=None)
    src=[i]
    for q in paths:src.extend([len(q),*q])
    command=[str(Path("adjacent-tree.exe").resolve()),str(target),str(budget),mode]
    if mode=="outer":command.extend(map(str,flips))
    proc=subprocess.run(command,
                        input=" ".join(map(str,src)),text=True,capture_output=True,check=True)
    idx,status,*raw=proc.stdout.split();assert int(idx)==i
    visits,arms,calls,n,*tail=map(int,raw);c=tail[:n];m,*d=tail[n:];assert len(d)==m
    hit=None
    if status=="FOUND":
        if mode=="prefix":A,B=paths[:2];C,D=c,d
        elif mode=="middle":A,B,C,D=c[::-1],paths[1],paths[2],d
        else:
            A,B,C,D=paths[0],c,d,paths[3]
            if flips[0]:A=A[::-1]
            if flips[1]:D=D[::-1]
        hit=A+[v|128 for v in B]+[v|384 for v in C]+[v|256 for v in D]
        assert len(hit)==target and not defects(hit)
    return dict(status=status,third_nodes=visits,last_nodes=arms,last_calls=calls,vertices=hit)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=100000000);p.add_argument("--mode",choices=("prefix","middle","outer"),default="prefix")
    a=p.parse_args();rows=[]
    for i,(_,axes,q) in enumerate(sources()):
        arrangements_here=list(arrangements(q))
        cases=[(p,(0,0)) for p in arrangements_here] if a.mode=="prefix" else [(arrangements_here[0],(0,0))]
        if a.mode=="outer":cases=[(arrangements_here[0],(a,b)) for a in (0,1) for b in (0,1)]
        for orientation,(paths,flips) in enumerate(cases):
            j=len(cases)*i+orientation
            if not a.first<=j<a.stop:continue
            ctrl=run(j,paths,191,1000000,a.mode);assert ctrl["status"]=="FOUND"
            res=run(j,paths,193,a.budget,a.mode,flips)
            rows.append(dict(index=j,source=i,orientation=orientation,axes=axes,flips=flips,**res))
            prefix="adjacent-tree" if a.mode=="prefix" else "adjacent-tree-"+a.mode
            save(Path(f"{prefix}-{a.first}-{a.stop}-{a.budget}.json"),rows)
            if res["vertices"]:break
        if rows and rows[-1]["vertices"]:break
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
