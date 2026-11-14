"""Free both anchored face paths by joining every feasible single-face edited order."""
from collections import Counter
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
import argparse,subprocess
from joint_parity import orders,representatives,assemble
from paired_seeds import extract
from solve import defects,save


@lru_cache(maxsize=None)
def portfolio(base,cap,count):
    proc=subprocess.run([str(exe),str(count),str(int(cap))],input=" ".join(map(str,base)),
                        capture_output=True,text=True,check=True)
    lines=proc.stdout.splitlines();tag,num,passed=lines.pop().split()
    assert tag=="count" and int(num)==comb(len(base)-1,count)*comb(128-len(base),count)
    assert int(passed)==len(lines)
    results=[]
    for line in lines:
        edits=list(map(int,line.split()))
        S=tuple(sorted(set(base)-set(edits[:count])|set(edits[count:])))
        possible=orders(S,cap)
        if possible:results.append((edits,set(S),possible))
    return results


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for v in ("left","right"):p.add_argument(v,type=int,choices=(1,2))
    p.add_argument("--exe",type=Path,default=Path("rooted-edits.exe"))
    a=p.parse_args();exe=a.exe.resolve();rows=[]
    for i,rec in enumerate(extract()):
        A=tuple(sorted(rec["parent"][::2]));B=tuple(sorted(rec["known_partner"][::2]))
        for cap in (0,1):
            L=portfolio(A,cap==0,a.left);R=portfolio(B,cap==1,a.right)
            stats=Counter();r=dict(index=i,cap=cap,orderable=[len(L),len(R)])
            for (ed1,S,paths),(ed2,T,others) in product(L,R):
                if S&T!={0}:continue
                stats["disjoint"]+=1
                for (x,ls),(y,rs) in product(paths,others):
                    stats["orders"]+=1
                    labels=representatives(ls+rs)
                    if labels is None:continue
                    q=assemble(x,labels[:len(ls)])[::-1]+[v|256 for v in assemble(y,labels[len(ls):])]
                    assert len(q)==193 and not defects(q)
                    r.update(witness=q,edits=[ed1,ed2]);break
                if "witness" in r:break
            r["stats"]=stats;rows.append(r)
            if "witness" in r:break
        if "witness" in rows[-1]:break
    save(Path(f"mixed-even-{a.left}-{a.right}.json"),rows)
    print(len(rows),sum((Counter(r["stats"]) for r in rows),Counter()),sum("witness" in r for r in rows),flush=True)
