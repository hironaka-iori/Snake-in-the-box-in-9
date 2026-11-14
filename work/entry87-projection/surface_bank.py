"""Search an entire bank range with independently variable projected positions."""
import argparse,json
from collections import Counter
from pathlib import Path
from punctured_lift import project
from surface_reroute import add_sites,solve_domain
from solve import BANK,BANK_HASH,sha256,save


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("width",type=int);p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=20000);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw)
    file=Path(f"surface-bank-{a.width}-{a.first}-{a.stop}-{a.budget}.json");rows=[]
    for i in range(a.first,a.stop):
        for b in range(9):
            tr,old=project(bank[i]["vertex_sequence"],b);dom=add_sites(tr,a.width)
            r=solve_domain(tr,dom,set(old),a.budget)
            rows.append(dict(source=i,axis=b,**r))
            if r["status"]=="FOUND":break
        save(file,rows);print(i,Counter(r["status"] for r in rows[-9:]),flush=True)
        if rows[-1]["status"]=="FOUND":break
