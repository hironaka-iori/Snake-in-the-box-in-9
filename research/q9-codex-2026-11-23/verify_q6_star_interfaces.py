"""Check catalogue coverage and replay star interface certificates."""
import argparse
import gzip
from itertools import islice
import json
from pathlib import Path

from q6_exact_anchored_profiles import catalogue
from q6_star_interfaces import check,formula


def verify(path,checker,first):
    proved=[]
    with gzip.open(path,"rt") as source:
        records=islice(source,first) if first is not None else source
        for line in records:
            row=json.loads(line)
            if row["status"]!="UNSAT_all_anchors_verified":
                continue
            e,c,leaves=row["key"]
            suffix="catalogue.log" if e==25 else "interfaces.log"
            anchors=list(catalogue(path.parent/f"q6_{e}_edge_{suffix}",c))
            assert [int(x["anchor"],16) for x in row["cases"]]==anchors and anchors
            for mask,case in zip(anchors,row["cases"]):
                assert case["status"]=="UNSAT_DRAT_verified"
                check(formula(mask,leaves),case["proof"],checker)
            proved.append(row["key"])
    return proved


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("archive",type=Path)
    p.add_argument("checker")
    p.add_argument("--first",type=int)
    a=p.parse_args()
    print(json.dumps(verify(a.archive,a.checker,a.first)))
