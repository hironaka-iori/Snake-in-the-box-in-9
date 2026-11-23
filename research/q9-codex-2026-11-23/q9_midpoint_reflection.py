"""Exact midpoint cubing modulo endpoint-preserving maps and path reversal."""
import argparse
from collections import defaultdict
import json
from pathlib import Path
import subprocess

from pysat.solvers import Cadical195, Cadical300, Glucose42

from q9_endpoint_lex import add_swap_lex
from q9_endpoint_distance_bound import read_path
from q9_midpoint_cases import midpoint_edges
from q9_modular_orientation import modular


def signature(x,y,end):
    flipped=x^y
    return ((x&end).bit_count(),(x&~end).bit_count(),bool(flipped&end),bool(x&flipped))


def representatives(distance):
    end=(1<<distance)-1
    for x,y in midpoint_edges(9,distance):
        key=signature(x,y,end)
        reflect=signature(y^end,x^end,end)
        if key<=reflect:
            yield x,y


def build(distance,x,y,halves=False,squares=False, cycle_span=0, outer=None):
    anchors=[(x,110),(y,111)]
    if outer:
        anchors.extend([(outer[0],109),(outer[1],112)])
    f,end=modular(9,221,distance,7,pair17=True,anchors=anchors,
                  anchor_distances=True,half_membership=halves)
    colors=defaultdict(list)
    for i in range(9):
        colors[tuple(v>>i&1 for v in (end,*(v for v,_ in anchors)))].append(i)
    add_swap_lex(f,9,(p for axes in colors.values() for p in zip(axes,axes[1:])))
    if squares:
        from q9_square_census import add_square_identity
        add_square_identity(f,9,222)
    if cycle_span:
        from q9_short_cycle_clauses import add_small_cycles
        add_small_cycles(f,9,cycle_span)
    return f,end


def run(distance,x,y,a):
    engines={"cadical195":Cadical195,"cadical300":Cadical300,"glucose42":Glucose42}
    f,end=build(distance,x,y,a.halves,a.square_census,a.cycle_span,getattr(a,"outer",None))
    row=dict(distance=distance,edge=[x,y],backend=a.solver,halves=a.halves,square_census=a.square_census,cycle_span=a.cycle_span,outer=getattr(a,"outer",None),budget=a.budget,
             clauses=len(f.clauses),variables=f.nv)
    print(json.dumps(dict(row,status="STARTED")),flush=True)
    with engines[a.solver](bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(a.budget)
        verdict=sat.solve_limited()
        if verdict is None:
            row["status"]="UNKNOWN"
        elif verdict:
            path=read_path(sat.get_model(),9,221,end)
            assert path[110:112]==[x,y]
            if row["outer"]:
                assert (path[109],path[112])==tuple(row["outer"])
            row.update(status="SAT_checked",path=path)
        else:
            mode="_halves" if a.halves else ""
            if a.square_census:
                mode+="_square"
            if a.cycle_span:
                mode+=f"_cycles{a.cycle_span}"
            if row["outer"]:
                mode+="_outer_"+"_".join(map(str,row["outer"]))
            stem=a.out/f"middle_reflect_d{distance}_{x}_{y}_{a.solver}{mode}"
            cnf,trace=stem.with_suffix(".cnf"),stem.with_suffix(".drat")
            f.to_file(str(cnf))
            trace.write_text("\n".join(sat.get_proof())+"\n")
            check=subprocess.run([a.checker,str(cnf),str(trace)],check=True,capture_output=True)
            assert b"s VERIFIED" in check.stdout
            row.update(status="UNSAT_DRAT_verified",trace=str(trace))
        return dict(row,**sat.accum_stats())


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("out",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--solver",choices=("cadical195","cadical300","glucose42"),default="cadical300")
    parser.add_argument("--budget",type=int,default=160000)
    parser.add_argument("--distance",type=int,choices=(3,5,7,9))
    parser.add_argument("--list",action="store_true")
    parser.add_argument("--halves",action="store_true")
    parser.add_argument("--square-census",action="store_true")
    parser.add_argument("--cycle-span",choices=(2,3,4),type=int,default=0)
    a=parser.parse_args()
    for d in ((a.distance,) if a.distance else (9,3,5,7)):
        for x,y in representatives(d):
            print(json.dumps(dict(distance=d,edge=[x,y]) if a.list else run(d,x,y,a)),flush=True)
