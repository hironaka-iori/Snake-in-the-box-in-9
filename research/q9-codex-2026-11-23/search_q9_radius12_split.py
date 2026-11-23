"""Split each unsolved endpoint case on retaining the radius-11 rim or omitting its first missing point."""
import argparse
import json
from pathlib import Path
from search_q9_endpoint_domains import cases,propagate,QuotaSolver,anchored,check

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("source",type=Path)
    ap.add_argument("--budget",type=int,default=20000)
    args=ap.parse_args()
    bank={(f,r):(p,i,j) for f,r,p,i,j,_ in cases()}
    for r in map(json.loads,args.source.read_text().splitlines()):
        if r["status"]!="UNKNOWN":continue
        p,i,j=bank[r["source"],r["row"]]
        missing=r["omitted"]
        centers=[0,len(p)-1,i,j,p.index(missing)]
        dist=[min(abs(k-c) for c in centers) for k in range(len(p))]
        assert r["width"]==12
        fixed={v for v,d in zip(p,dist) if d>12}
        rim=[v for v,d in zip(p,dist) if d==12]
        for excluded in [*rim,None]:
            banned={missing} if excluded is None else {missing,excluded}
            case=propagate(fixed,banned,r["sig"])
            minimum=192+int(r["sig"]==2)
            if case is None:s,w="GEOMETRY",None
            else:
                f,a=case
                anchored.Minicard=lambda:QuotaSolver(f,a,minimum,r["sig"])
                s,w=anchored.search(f,set(p),minimum,args.budget,allowed=a,at_least=True)
            if w:
                check(w,192)
                assert fixed<=set(w) and banned.isdisjoint(w)
            print(json.dumps({**r,"rim":rim,"second_omission":excluded,
                              "status":s,"witness":w}),flush=True)
            if w:return
            if excluded is not None:fixed.add(excluded)
if __name__=="__main__":main()
