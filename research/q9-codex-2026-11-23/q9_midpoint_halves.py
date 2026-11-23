"""Exact midpoint cases via two separate induced paths and a single bridge."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.formula import CNF
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_free_pair_cuts import add_pair_cuts
from q9_midpoint_cases import midpoint_edges
from q9_modular_orientation import modular


def add_half(f,dim,length,origin,destination,offset):
    n=1<<dim
    delta=origin^destination
    distance=delta.bit_count()
    axes=sorted(range(dim),key=lambda i:not (delta>>i&1))
    local,_=modular(dim,length,distance,max(1,(length//2).bit_length()),
                    anchor_distances=True)
    points=[0]*n
    for local_v in range(n):
        cube_v=origin^sum(((local_v>>i)&1)<<axis for i,axis in enumerate(axes))
        points[cube_v]=offset+local_v+1
    f.extend([(offset+x if x>0 else x-offset) for x in clause] for clause in local.clauses)
    return points,offset+local.nv


def formula(dim,length,endpoint,x,y,pair17):
    n=1<<dim
    assert length%2==1 and (x^y).bit_count()==1
    f=CNF()
    left,offset=add_half(f,dim,length//2,0,x,n)
    right,_=add_half(f,dim,length//2,endpoint,y,offset)
    for v in range(n):
        f.extend([[-left[v],-right[v]],[-left[v],v+1],[-right[v],v+1],
                  [-v-1,left[v],right[v]]])
        for i in range(dim):
            w=v^(1<<i)
            if (v,w)!=(x,y):
                f.append([-left[v],-right[w]])
    if pair17:
        add_pair_cuts(f,f.nv,minimum=17)
    return f


def run(d,x,y,args):
    endpoint=(1<<d)-1
    f=formula(9,221,endpoint,x,y,True)
    row=dict(distance=d,edge=[x,y],variables=f.nv,clauses=len(f.clauses),budget=args.budget)
    print(json.dumps(dict(row,status="STARTED")),flush=True)
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(args.budget)
        ans=sat.solve_limited()
        if ans is None:
            row["status"]="UNKNOWN"
        elif ans:
            path=read_path(sat.get_model(),9,221,endpoint)
            assert path[110:112]==[x,y]
            row.update(status="SAT_checked",path=path)
        else:
            stem=args.out/f"halves_d{d}_{x}_{y}"
            cnf,trace=stem.with_suffix(".cnf"),stem.with_suffix(".drat")
            f.to_file(str(cnf))
            trace.write_text("\n".join(sat.get_proof())+"\n")
            verified=subprocess.run([args.checker,str(cnf),str(trace)],check=True,capture_output=True)
            assert b"s VERIFIED" in verified.stdout
            row.update(status="UNSAT_DRAT_verified",trace=str(trace))
        return dict(row,**sat.accum_stats())


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    p.add_argument("--budget",type=int,default=160000)
    p.add_argument("--distance",type=int,default=9)
    a=p.parse_args()
    for x,y in midpoint_edges(9,a.distance):
        print(json.dumps(run(a.distance,x,y,a)),flush=True)
