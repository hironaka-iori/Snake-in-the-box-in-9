"""Decide the open first-root branches independently for each possible second crossing."""
import argparse,json
from collections import Counter
from pathlib import Path
from crossing_pair_filter import pair_rows
from punctured_lift import project
from single_hinge_exchange import search
from solve import BANK,BANK_HASH,sha256,save

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("source",type=int);p.add_argument("--budget",type=int,default=250000);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw)
    P,sw=project(bank[a.source]["vertex_sequence"],5);assert len(sw)==1
    old=json.loads(Path(f"single-hinge-exchange-{a.source}-300000-remove2-cross2.json").read_bytes())
    open_roots={z["root"] for z in old["results"] if z["status"]=="OPEN"}
    pairs=[tuple(z["roots"]) for z in pair_rows(P) if z["roots"][0] in open_roots]
    result=search(P,a.budget,crossings=2,removals=2,root_pairs=pairs) if pairs else []
    save(Path(f"two-crossing-pairs-{a.source}-{a.budget}.json"),dict(source=a.source,
         open_first_roots=sorted(open_roots),pairs=pairs,results=result))
    print(a.source,len(pairs),Counter(z["status"] for z in result),flush=True)
