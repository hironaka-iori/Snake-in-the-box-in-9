"""Replay each local signature rejection before using it in a larger projection."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.formula import CNF

from q6_exact_anchored_profiles import catalogue
from q6_exact_interface_profiles import formula
from verify_q9_free_dimension_cuts import parts,deg


def verify(files,checker):
    proved=set()
    for path in files:
        for line in path.read_text().splitlines():
            row=json.loads(line)
            if row["status"]!="UNSAT_all_anchors_verified":
                continue
            e,c=row["key"][0]
            table=path.parent/f"q6_{e}_edge_{'catalogue.log' if e==25 else 'interfaces.log'}"
            anchors=list(catalogue(table,c))
            actual=[int(r["anchor"],16) for r in row["cases"]]
            assert actual==anchors
            for case,anchor in zip(row["cases"],anchors):
                assert case["status"]=="UNSAT_DRAT_verified"
                f=formula(row["key"],anchor)
                for cycle in case["cycles"]:
                    points=set(cycle)
                    assert len(points)==len(cycle) and all(0<=v<128 for v in points)
                    assert len(parts(points,7))==1 and all(deg(points,v,7)==2 for v in points)
                    f.append([-v-1 for v in cycle])
                trace=Path(case["trace"])
                cnf=trace.with_suffix(".cnf")
                original=CNF(from_file=str(cnf))
                assert original.clauses==f.clauses
                r=subprocess.run([checker,str(cnf),str(trace)],check=True,capture_output=True)
                assert b"s VERIFIED" in r.stdout
            a,b,r=row["key"]
            proved.add((tuple(a),tuple(b),r))
    return sorted(proved)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("checker")
    p.add_argument("files",type=Path,nargs="+")
    a=p.parse_args()
    print(json.dumps(verify(a.files,a.checker)))
