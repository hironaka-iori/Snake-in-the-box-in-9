"""Compare native two-even replacements to the face matching theorem."""
import argparse
from itertools import product
from math import comb
from pathlib import Path
import subprocess
from joint_parity import orders
from paired_seeds import extract
from solve import defects,save


def run(a):
    rows=[];bank=extract()
    for index in range(a.start,a.stop):
        s=bank[index];sets=[sorted(s["parent"][::2]),sorted(s["known_partner"][::2])]
        data=" ".join(map(str,[len(sets[0]),*sets[0],len(sets[1]),*sets[1]]))
        for cap,changing in product((0,1),repeat=2):
            proc=subprocess.run([str(a.exe.resolve()),str(cap),str(changing)],input=data,text=True,
                                capture_output=True,check=True)
            fields=proc.stdout.split()
            row=dict(index=index,cap=cap,changed_side=changing)
            if fields[0]=="witness":
                q=list(map(int,fields[1:]))
                assert len(q)==193 and not defects(q)
                halves=([v for v in q if v<256],[v-256 for v in q if v>=256])
                even=[{v for v in h if v.bit_count()%2==0} for h in halves]
                assert len(set(sets[changing])-even[changing])==2 and even[1-changing]==set(sets[1-changing])
                row["witness"]=q
            elif fields[0]=="fixed-impossible":
                assert not orders(tuple(sets[1-changing]),cap==1-changing)
                row["fixed_impossible"]=True
            else:
                assert fields[0]=="count"
                cases,ok,orderable,pairs=map(int,fields[1:])
                assert cases==comb(len(sets[changing])-1,2)*comb(32,2)
                row.update(cases=cases,first_filter=ok,orderable=orderable,pairs=pairs)
            rows.append(row)
            if "witness" in row:break
        if "witness" in rows[-1]:break
    save(Path(f"joint-even-two-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum(x.get("cases",0) for x in rows),sum(x.get("pairs",0) for x in rows),
          sum("witness" in x for x in rows),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--exe",type=Path,default=Path("joint-even-edges.exe"));run(p.parse_args())
