"""Check a projected count motif by a second, exact geometry encoding."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.solvers import Cadical195
from q9_window_geometry_certificate import formula


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("checker")
    p.add_argument("motifs",type=Path,nargs="+")
    a=p.parse_args()
    for path in a.motifs:
        data=json.loads(path.read_text())
        cnf=formula(data["layers"])
        row=dict(start=data["start"],stop=data["stop"],steps=len(data["layers"])+8)
        with Cadical195(bootstrap_with=cnf,with_proof=True) as sat:
            if sat.solve():
                row["status"]="SAT_local_path"
            else:
                model=path.with_suffix(".cnf")
                proof=path.with_suffix(".drat")
                cnf.to_file(str(model))
                proof.write_text("\n".join(sat.get_proof())+"\n")
                r=subprocess.run([a.checker,str(model),str(proof)],check=True,capture_output=True)
                assert b"s VERIFIED" in r.stdout
                row.update(status="UNSAT_DRAT_verified",proof=str(proof))
            print(json.dumps(dict(row,**sat.accum_stats())),flush=True)
