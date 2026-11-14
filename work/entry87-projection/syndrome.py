"""Restrict the cube-neighbour parity syndrome, leaving both path orders free."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
from source_growth import check
from solve import BANK,BANK_HASH,defects,save


def neighbour_syndrome(S):
    return {x for x in range(512) if sum((x^(1<<b)) in S for b in range(9))%2}


def run(a):
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);memo={};rows=[]
    for index in range(a.start,a.stop):
        path=bank[index]["vertex_sequence"]
        for p in (0,1):
            anchors=tuple(sorted(path[p::2]));caps=a.radius%2==0
            if anchors in memo:
                rows.append(dict(index=index,parity=p,duplicate=memo[anchors]));continue
            memo[anchors]=[index,p]
            old=neighbour_syndrome(set(anchors))
            assert neighbour_syndrome(old)==set(anchors)
            cmd=[str(a.exe.resolve()),str(p),str(a.radius),"0","256"]
            proc=subprocess.run(cmd,input=" ".join(map(str,anchors)),text=True,capture_output=True,check=True)
            lines=proc.stdout.splitlines()
            label,trials,sizes,degree,connected=lines.pop().split()
            assert label=="count" and int(trials)==comb(256,a.radius) and len(lines)==int(connected)
            stats=Counter();hard=[];row=dict(index=index,parity=p,trials=int(trials),sizes=int(sizes),
                                             degree=int(degree),connected=int(connected))
            for line in lines:
                changed=list(map(int,line.split()))
                target=set(anchors)^neighbour_syndrome(set(changed))
                assert len(target)==(96 if caps else 97)
                assert neighbour_syndrome(target)==old^set(changed)
                reason,w=check(target,caps);stats[reason]+=1
                assert reason not in ("disconnected","endpoint degrees")
                if reason=="Hamilton path infeasible":hard.append(changed)
                if w:
                    assert not defects(w)
                    row.update(syndrome_change=changed,witness=w);break
            row.update(stats=stats,hard=hard);rows.append(row)
            if row.get("witness"):break
        if rows[-1].get("witness"):
            print("WITNESS",index,flush=True);break
    save(Path(f"syndrome-{a.radius}-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum(r.get("sizes",0) for r in rows),sum(r.get("connected",0) for r in rows),
          sum((Counter(r.get("stats",{})) for r in rows),Counter()),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for n in ("radius","start","stop"):p.add_argument(n,type=int)
    p.add_argument("--exe",type=Path,default=Path("syndrome.exe"))
    run(p.parse_args())
