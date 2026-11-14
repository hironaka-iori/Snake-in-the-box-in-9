import argparse,json
from collections import Counter
from math import comb
from pathlib import Path
import subprocess
from paired_seeds import extract
from joint_parity import test
from solve import save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--exe",type=Path,default=Path("targeted-even-three.exe"));a=p.parse_args()
    known=extract();hall=json.loads(Path("joint-hall.json").read_text());rows=[]
    for h in hall:
        i=h["index"];cap=h["odd_end_on"]
        if not a.start<=i<a.stop or not h["hall"]:continue
        r=known[i];sets=[set(r["parent"][::2]),set(r["known_partner"][::2])]
        data=" ".join(map(str,[len(sets[0]),*sorted(sets[0]),len(sets[1]),*sorted(sets[1])]))
        for w in sorted({v for j in h["hall"] for v in j["addresses"]}):
            for side in (0,1):
                cmd=[str(a.exe.resolve()),str(cap),str(side),str(w)]
                proc=subprocess.run(cmd,input=data,text=True,capture_output=True,check=True)
                lines=proc.stdout.splitlines()
                tag,cases,filtered,n=lines.pop().split();n=int(n)
                assert tag=="count" and int(filtered)==len(lines)
                assert int(cases)==comb(len(sets[side])-1,3)*(comb(32,3)-comb(32-n,3))
                stats=Counter();out=dict(index=i,cap=cap,side=side,address=w,trials=int(cases),filtered=len(lines))
                for line in lines:
                    edits=list(map(int,line.split()));new=sets[side]-set(edits[:3])|set(edits[3:])
                    assert len(new)==len(sets[side])
                    pair=sets.copy();pair[side]=new;q=test(*pair,cap,stats)
                    if q:out.update(witness=q,edit=edits);break
                out["stats"]=stats;rows.append(out)
                if "witness" in out:break
            if "witness" in rows[-1]:break
        if "witness" in rows[-1]:break
    save(Path(f"targeted-even-three-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum(r["trials"] for r in rows),sum(r["filtered"] for r in rows),
          sum("witness" in r for r in rows),flush=True)
