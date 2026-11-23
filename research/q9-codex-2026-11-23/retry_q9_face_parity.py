"""Retry unresolved face searches by solving both possible endpoint colors."""
import argparse
from collections import Counter
import json
from pathlib import Path
from search_q9_face_sat import check_face

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("bank",type=Path)
    ap.add_argument("first_pass",type=Path)
    ap.add_argument("output",type=Path)
    ap.add_argument("--budget",type=int,default=200000)
    args=ap.parse_args()
    paths=[r["vertex_sequence"] for r in json.loads(args.bank.read_text())]
    stats=Counter()
    with args.first_pass.open() as first, args.output.open("x") as output:
        for line in first:
            r=json.loads(line)
            if r["status"]!="UNKNOWN":continue
            free={v for v in range(512) if v&r["mask"]==r["base"]}
            outcome=[]
            for parity in (0,1):
                status,w=check_face(paths[r["seed"]],free,192,args.budget,parity)
                outcome.append(status)
                if w is not None:
                    r.update(status="FOUND",vertices=w,parity=parity)
                    print(json.dumps(r),file=output,flush=True)
                    print(json.dumps(r),flush=True)
                    return
            r.update(status="UNSAT" if outcome==["UNSAT","UNSAT"] else "UNKNOWN",by_parity=outcome)
            print(json.dumps(r),file=output,flush=True)
            stats[r["status"]]+=1
    print(dict(stats),flush=True)

if __name__=="__main__":
    main()
