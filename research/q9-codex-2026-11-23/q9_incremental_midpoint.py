"""Reuse learned clauses across sibling midpoint cubes and replay terminal proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from pysat.formula import CNF
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_midpoint_neighborhood import neighbors
from q9_midpoint_reflection import representatives
from q9_modular_orientation import modular
from q9_short_cycle_clauses import add_small_cycles
from q9_square_census import add_square_identity


def parent(distance,x,y):
    # Do not impose lex comparisons that move the outer vertices between siblings.
    f,end=modular(9,221,distance,7,pair17=True,anchors=[(x,110),(y,111)],anchor_distances=True)
    add_small_cycles(f,9,3)
    add_square_identity(f,9,222)
    return f,end


def verify_leaf(f,units,budget,stem,checker):
    instance=CNF(from_clauses=f.clauses+[[v] for v in units])
    with Cadical195(bootstrap_with=instance,with_proof=True) as sat:
        sat.conf_budget(budget)
        verdict=sat.solve_limited()
        if verdict is None:
            return dict(status="UNSAT_reproof_pending")
        assert verdict is False
        cnf,trace=stem.with_suffix(".cnf"),stem.with_suffix(".drat")
        instance.to_file(str(cnf))
        trace.write_text("\n".join(sat.get_proof())+"\n")
        result=subprocess.run([checker,str(cnf),str(trace)],check=True,capture_output=True)
        assert b"s VERIFIED" in result.stdout
        return dict(status="UNSAT_DRAT_verified",proof=str(trace))


def queue(args):
    completed=set()
    if args.report.exists():
        for line in args.report.read_text().splitlines():
            row=json.loads(line)
            # Resume only an identical budget/model and never turn UNKNOWN into UNSAT.
            if row.get("budget")==args.budget and row["status"] in (
                    "UNKNOWN","UNSAT_DRAT_verified","SAT_checked"):
                completed.add((row["model"],row["distance"],tuple(row["edge"]),tuple(row["outer"])))
    with args.report.open("a") as report:
        for distance in args.distances:
            for x,y in representatives(distance):
                f,end=parent(distance,x,y)
                digest=hashlib.sha256()
                for clause in f.clauses:
                    digest.update((" ".join(map(str,clause))+" 0\n").encode())
                model=digest.hexdigest()
                with Cadical195(bootstrap_with=f) as sat:
                    for index,(prev,nxt) in enumerate(neighbors(distance,x,y)):
                        key=(model,distance,(x,y),(prev,nxt))
                        if key in completed:
                            continue
                        before=sat.accum_stats()["conflicts"]
                        row=dict(model=model,distance=distance,edge=[x,y],outer=[prev,nxt],
                                 budget=args.budget,sibling=index,previous_conflicts=before)
                        print(json.dumps(dict(row,status="STARTED")),flush=True)
                        # Selected neighbors of ordered midpoint vertices must be at 109 and 112.
                        units=[prev+1,nxt+1]
                        sat.conf_budget(args.budget)
                        verdict=sat.solve_limited(assumptions=units)
                        row["conflicts"]=sat.accum_stats()["conflicts"]-before
                        if verdict is None:
                            row["status"]="UNKNOWN"
                        elif verdict:
                            path=read_path(sat.get_model(),9,221,end)
                            assert path[109:113]==[prev,x,y,nxt]
                            row.update(status="SAT_checked",path=path)
                        else:
                            stem=args.report.parent/f"incremental_d{distance}_{x}_{y}_{prev}_{nxt}"
                            row.update(verify_leaf(f,units,8*args.budget,stem,args.checker))
                        report.write(json.dumps(row)+"\n")
                        report.flush()
                        print(json.dumps(row),flush=True)
                        if row["status"]=="SAT_checked":
                            return


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("report",type=Path)
    p.add_argument("checker")
    p.add_argument("--distances",nargs="+",type=int,choices=(3,5,7,9),default=[9,3,5,7])
    p.add_argument("--budget",type=int,default=160000)
    queue(p.parse_args())
