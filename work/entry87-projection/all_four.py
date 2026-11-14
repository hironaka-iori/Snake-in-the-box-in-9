"""Run rank four on each distinct real bank side, with no face limitation."""
import argparse,json,subprocess
from pathlib import Path
from solve import BANK,BANK_HASH,sha256,save

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    groups={}
    for i,r in enumerate(json.loads(raw)):
        for parity in (0,1):
            group=tuple(sorted(r["vertex_sequence"][parity::2]))
            groups.setdefault(group,[]).append([i,parity])
    unique=list(groups.values())
    rows=[]
    for copies in unique[a.start:a.stop]:
        i,p=copies[0];file=Path(f"syndrome-four-{i}-{p}-0-256.json")
        if not file.exists():
            subprocess.run(["py","-3.11","syndrome_four.py",str(i),str(p),"0","256"],check=True)
        r=json.loads(file.read_text());rows.append(dict(occurrences=copies,**r))
        if any(x["witness"] for x in r["results"]):break
    save(Path(f"syndrome-four-bank-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum(r["tuples"] for r in rows),sum(r["connected"] for r in rows),flush=True)
