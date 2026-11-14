import argparse
from collections import Counter
from math import comb
from pathlib import Path
import json,subprocess
from syndrome import neighbour_syndrome
from source_growth import check
from solve import BANK,BANK_HASH,sha256,save


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for s in ("entry","parity","start","stop"):p.add_argument(s,type=int)
    p.add_argument("--exe",type=Path,default=Path("syndrome-four.exe"));a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    S=set(json.loads(raw)[a.entry]["vertex_sequence"][a.parity::2])
    proc=subprocess.run([str(a.exe.resolve()),str(a.parity),str(a.start),str(a.stop)],
        input=" ".join(map(str,sorted(S))),text=True,capture_output=True,check=True)
    lines=proc.stdout.splitlines();tag,triples,tuples,near,size,degree,connected=lines.pop().split()
    assert tag=="count" and int(tuples)==sum(comb(255-i,3) for i in range(a.start,a.stop))
    assert len(lines)==int(connected)
    results=[]
    for l in lines:
        edit=list(map(int,l.split()));new=S^neighbour_syndrome(set(edit))
        assert len(new)==96 and neighbour_syndrome(new)==neighbour_syndrome(S)^set(edit)
        reason,w=check(new,True);results.append(dict(edit=edit,reason=reason,witness=w))
    row=dict(entry=a.entry,parity=a.parity,start=a.start,stop=a.stop,triples=int(triples),tuples=int(tuples),
             near=int(near),size=int(size),degree=int(degree),connected=int(connected),results=results)
    save(Path(f"syndrome-four-{a.entry}-{a.parity}-{a.start}-{a.stop}.json"),row)
    print(row["tuples"],row["near"],row["size"],row["degree"],Counter(r["reason"] for r in results),flush=True)
