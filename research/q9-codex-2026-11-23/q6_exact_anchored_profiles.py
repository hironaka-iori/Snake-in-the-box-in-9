"""Use exhaustive six-dimensional catalogues to cover hard interface signatures."""
import argparse
import json
from pathlib import Path

from q6_exact_interface_profiles import run,signatures


def catalogue(path,c):
    for line in path.read_text().splitlines():
        fields=line.split()
        if fields[0]=="representative" and int(fields[1])==c:
            yield int(fields[-1],16)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("profiles",type=Path)
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    p.add_argument("--max-cases",type=int,default=12)
    a=p.parse_args()
    for key in [k for k in signatures(a.profiles) if k[0][0] in (25,26)][:a.max_cases]:
        e,c=key[0]
        name=f"q6_{e}_edge_"+("catalogue.log" if e==25 else "interfaces.log")
        anchors=list(catalogue(a.out/name,c))
        assert anchors
        print(json.dumps(dict(key=key,anchors=len(anchors),status="STARTED")),flush=True)
        cases=[]
        for anchor in anchors:
            found=run(key,20000,a.out,a.checker,anchor)
            cases.append(dict(anchor=f"{anchor:016x}",**found))
            if found["status"]=="SAT_checked":
                break
        state=("SAT_checked" if cases[-1]["status"]=="SAT_checked"
               else "UNSAT_all_anchors_verified" if all(r["status"]=="UNSAT_DRAT_verified" for r in cases)
               else "UNKNOWN")
        print(json.dumps(dict(key=key,status=state,cases=cases)),flush=True)
