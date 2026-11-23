"""Cover the four endpoint-distance orbits by their oriented middle edge."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_modular_orientation import modular


def midpoint_edges(dim, distance):
    """Enumerate one representative under each endpoint-preserving coordinate orbit."""
    end=(1<<distance)-1
    first=list(range(distance))
    second=list(range(distance,dim))
    for within in (True,False):
        block=first if within else second
        if not block:
            continue
        axis=block[0]
        normal_first=[i for i in first if i!=axis]
        normal_second=[i for i in second if i!=axis]
        for a in range(len(normal_first)+1):
            for b in range(len(normal_second)+1):
                for bit in (0,1):
                    if (a+b+bit)%2:
                        continue
                    x=sum(1<<i for i in normal_first[:a]+normal_second[:b]) | (bit<<axis)
                    y=x^(1<<axis)
                    if min(x.bit_count(), y.bit_count(),
                           (x^end).bit_count(), (y^end).bit_count())<2:
                        continue
                    yield x,y


def run(d,x,y,budget,output,checker,tighten=False):
    f,end=modular(9,221,d,7,pair17=True,anchors=[(x,110),(y,111)],anchor_distances=tighten)
    # When the path is recovered, the anchored residues identify its actual positions:
    # all positions are in [0,221], which is smaller than the period 256.
    row=dict(distance=d,edge=[x,y],tighten=tighten,variables=f.nv,clauses=len(f.clauses),budget=budget)
    print(json.dumps(dict(row,status="STARTED")),flush=True)
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(budget)
        result=sat.solve_limited()
        if result is None:
            row.update(status="UNKNOWN")
        elif result:
            path=read_path(sat.get_model(),9,221,end)
            assert path[110:112]==[x,y]
            row.update(status="SAT_checked",path=path)
        else:
            stem=output/(f"middle_d{d}_{x}_{y}" + ("_tight" if tighten else ""))
            cnf,trace=stem.with_suffix(".cnf"),stem.with_suffix(".drat")
            f.to_file(str(cnf))
            trace.write_text("\n".join(sat.get_proof())+"\n")
            check=subprocess.run([checker,str(cnf),str(trace)],check=True,capture_output=True)
            assert b"s VERIFIED" in check.stdout
            row.update(status="UNSAT_DRAT_verified",trace=str(trace))
        return dict(row,**sat.accum_stats())


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    p.add_argument("--budget",type=int,default=80000)
    p.add_argument("--list",action="store_true")
    p.add_argument("--tighten", action="store_true")
    p.add_argument("--distance", type=int, choices=(3,5,7,9))
    a=p.parse_args()
    for d in ((a.distance,) if a.distance else (9,3,5,7)):
        for x,y in midpoint_edges(9,d):
            if a.list:
                print(json.dumps(dict(distance=d,edge=[x,y])))
            else:
                print(json.dumps(run(d,x,y,a.budget,a.out,a.checker,a.tighten)),flush=True)
