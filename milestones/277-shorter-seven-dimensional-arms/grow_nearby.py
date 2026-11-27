"""Seek 97- and 98-edge Q8 donors retaining all but at most one site of each census path."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
import sys
from enumerate_groups import HERE,MS,read,write,paircheck,unrooted,points
from summarize import old_pool
sys.path.insert(0,str(MS/"274-rebuilding-near-a-fixed-arm"))
from near import assemble

def main():
    ap=ArgumentParser();ap.add_argument("--count",type=int,default=1000000)
    ap.add_argument("--mode",choices=["single","double"],default="single")
    ap.add_argument("--source",choices=["direct","shortened"],default="direct");a=ap.parse_args()
    census=read(HERE/("q8-arms.json" if a.source=="direct" else "shorter-witnesses.json"))
    out=HERE/("nearby-"+a.source+"-"+a.mode+"-parents.json");hist=HERE/("nearby-"+a.source+"-"+a.mode+"-scans.json")
    ledger=read(hist) if hist.exists() else {};records=read(out) if out.exists() else {}
    old=set().union(*(r["words"] for r in old_pool().values()))
    targets=[k for k in sorted(census,key=lambda x:(-len(x),x)) if k not in ledger][:a.count]
    for w in targets:
        p=bytes(census[w]["joined_q8"]);collected=Counter()
        digest=sha256()
        choices=[()]+[(i,) for i in range(len(p))] if a.mode=="single" else combinations(range(len(p)),2)
        for omission in choices:
            for q in sorted(assemble(p,omission,97,98)):
                assert set(p)-set(q)=={p[i] for i in omission}
                pairs=paircheck(q,8);k=unrooted(q);n=len(q)-1
                assert 97<=n<=98
                digest.update(bytes([len(omission),*omission,len(q)])+q)
                collected[n]+=1
                if k not in records:
                    records[k]=dict(q8_edges=n,joined_q8=list(q),source=w,omitted_indices=list(omission),all_pairs=pairs,
                                    in_direct=k in census,in_previous_pool=k in old)
        ledger[w]=dict(lengths=collected,sha256=digest.hexdigest())
        if len(ledger)%20==0:
            write(out,records);write(hist,ledger)
            print("Inspected",len(ledger),"parents;",len(records),"long shapes",flush=True)
    write(out,records);write(hist,ledger)
    print("Complete sources",len(ledger),"/",len(census),"long shapes",dict(Counter(v["q8_edges"] for v in records.values())),
          "new outside direct and old",sum(not r["in_previous_pool"] and not r["in_direct"] for r in records.values()),flush=True)

if __name__=="__main__":main()
