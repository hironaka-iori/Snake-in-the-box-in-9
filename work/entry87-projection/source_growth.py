"""Free the chronology of each actual 191-edge bank snake and enlarge one parity."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import comb
from pathlib import Path
import subprocess
from parity_edits import force
from parity_skeleton import complete
from solve import BANK,BANK_HASH,defects,save


def check(anchors,caps):
    why,_=force(anchors,caps)
    if why:return why,None
    r=complete(anchors,caps)
    if r["status"]=="EXCLUDED":return r["reason"],None
    q=r["vertices"];assert len(q)==193 and not defects(q)
    return "FOUND",q


def run(a):
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);memo={};rows=[]
    for i in range(a.start,a.stop):
        source=bank[i]["vertex_sequence"]
        assert len(source)==192 and not defects(source)
        for p in (0,1):
            anchors=tuple(sorted(source[p::2]))
            assert len(anchors)==96 and all(x.bit_count()%2==p for x in anchors)
            if anchors in memo:
                rows.append(dict(index=i,parity=p,duplicate=memo[anchors]));continue
            memo[anchors]=[i,p]
            # Interpret this same set first as the smaller class of a target.
            small,w=check(anchors,True)
            row=dict(index=i,parity=p,small_class=small)
            if w:
                row["witness"]=w;rows.append(row);break
            native=subprocess.run([str(a.exe.resolve()),str(p),"0","96",str(3+a.remove)],
                                  input=" ".join(map(str,anchors)),capture_output=True,text=True,check=True)
            lines=native.stdout.splitlines();tag,tests,degree,connected,skip=lines.pop().split()
            assert tag=="count" and len(lines)==int(connected) and skip=="0"
            assert int(tests)==comb(96,a.remove)*comb(160,1+a.remove)
            reasons=Counter();hard=[]
            for line in lines:
                edits=list(map(int,line.split()))
                v=sorted(set(anchors)-set(edits[:a.remove])|set(edits[a.remove:]))
                assert len(v)==97
                reason,w=check(v,False);reasons[reason]+=1
                assert reason not in ("disconnected","endpoint degrees")
                if reason=="Hamilton path infeasible":hard.append(edits)
                if w:
                    row.update(witness=w,edit=edits);break
            row.update(tests=int(tests),degree_pass=int(degree),connected=int(connected),reasons=reasons,hard=hard)
            rows.append(row)
            if w:break
        if rows[-1].get("witness"):
            print("WITNESS",i,rows[-1]["parity"],flush=True);break
    save(Path(f"source-growth-{a.remove}-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum(r.get("tests",0) for r in rows),sum(r.get("connected",0) for r in rows),
          sum((Counter(r.get("reasons",{})) for r in rows),Counter()),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    for n in ("start","stop","remove"):parser.add_argument(n,type=int)
    parser.add_argument("--exe",type=Path,default=Path("growth-parity.exe"))
    run(parser.parse_args())
