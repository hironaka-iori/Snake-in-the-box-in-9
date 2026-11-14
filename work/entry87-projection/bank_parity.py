"""Test all one-chord bank walks with free order and one prescribed parity set."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
from parity_edits import force
from parity_skeleton import complete
from solve import BANK, BANK_HASH, defects, save


def inputs():
    raw=BANK.read_bytes()
    assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw)
    entries=json.loads(Path("bank-pivots.json").read_text())
    for index,row in enumerate(entries):
        path=bank[row["entry"]]["vertex_sequence"]
        t=row["insertion"];bit=1<<row["flip"]
        q=path[:t+1]+[v^bit for v in path[t:]]
        assert len(q)==193 and defects(q)==[tuple(row["chord"])]
        yield index,q


def finish(anchors,parity):
    reason,_=force(anchors,bool(parity))
    if reason:return reason,None
    report=complete(anchors,bool(parity))
    if report["status"]=="EXCLUDED":return report["reason"],None
    path=report["vertices"]
    assert len(path)==193 and not defects(path) and set(path[parity::2])==set(anchors)
    return "FOUND",path


def survey(first,stop,radius,exe):
    memo={};rows=[]
    for index,q in inputs():
        if not first<=index<stop:continue
        for parity in (0,1):
            anchors=tuple(sorted(q[parity::2]))
            if anchors in memo:
                rows.append(dict(index=index,parity=parity,duplicate=memo[anchors]))
                continue
            memo[anchors]=[index,parity]
            status,w=finish(anchors,parity)
            row=dict(index=index,parity=parity,unchanged=status)
            if w:row["witness"]=w
            if radius and not w:
                run=subprocess.run([str(exe),str(parity),"0",str(len(anchors)),
                                    "2" if radius==1 else "0"],text=True,capture_output=True,
                                   input=" ".join(map(str,anchors)),check=True)
                lines=run.stdout.splitlines()
                tag,attempts,degrees,connected,skip=lines.pop().split()
                assert (tag,int(connected),int(skip))==("count",len(lines),0)
                assert int(attempts)==comb(len(anchors),radius)*comb(256-len(anchors),radius)
                stats=Counter();remnants=[]
                for line in lines:
                    edit=list(map(int,line.split()))
                    edited=sorted(set(anchors)-set(edit[:radius])|set(edit[radius:]))
                    assert len(edited)==len(anchors)
                    reason,w=finish(edited,parity)
                    assert reason not in ("disconnected","endpoint degrees")
                    stats[reason]+=1
                    if reason not in ("degree contradiction","forced proper cycle"):
                        remnants.append([edit,reason])
                    if w:
                        row.update(witness=w,change=edit)
                        break
                row.update(cases=int(attempts),degree_pass=int(degrees),
                           connected_degree_pass=int(connected),counts=stats,exceptions=remnants)
            rows.append(row)
            if row.get("witness"):break
        if rows[-1].get("witness"):
            print("WITNESS",index,rows[-1]["parity"],flush=True)
            break
    save(Path(f"bank-parity-{radius}-{first}-{stop}.json"),rows)
    print(radius,first,stop,len(rows),sum(r.get("cases",0) for r in rows),
          sum(r.get("connected_degree_pass",0) for r in rows),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("first",type=int)
    parser.add_argument("stop",type=int)
    parser.add_argument("radius",type=int,choices=(0,1,2))
    parser.add_argument("--exe",type=Path,default=Path("two-parity-bank.exe"))
    a=parser.parse_args();survey(a.first,a.stop,a.radius,a.exe.resolve())
