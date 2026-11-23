"""Lift one aggregate triple projection to the exact 221-edge Q9 SAT model."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_modular_orientation import modular


def bind_projection(f, row):
    # The first three coordinates specify the layer. The other six specify a column.
    pool=IDPool(start_from=f.nv+1)
    for face,(e,c) in enumerate(zip(row["edges"],row["components"])):
        selected=[face+8*v+1 for v in range(64)]
        bounds=CardEnc.equals(selected,e+c,vpool=pool,encoding=EncType.cardnetwrk)
        f.extend(bounds.clauses)
    interface=0
    for axis in range(3):
        for a in range(8):
            b=a^(1<<axis)
            if a>b:
                continue
            overlaps=[]
            for v in range(64):
                x,y=a+8*v+1,b+8*v+1
                if row["crossings"][interface]==0:
                    f.append([-x,-y])
                    continue
                edge=pool.id()
                f.extend([[-edge,x],[-edge,y],[edge,-x,-y]])
                overlaps.append(edge)
            if overlaps:
                f.extend(CardEnc.equals(overlaps,row["crossings"][interface],
                                        vpool=pool,encoding=EncType.cardnetwrk).clauses)
            interface+=1


def run(row, budget, prefix, checker):
    assert row["counts"]==[9,9,9] and row["end"]==7
    f,end=modular(9,221,9,7,pair17=True)
    bind_projection(f,row)
    print(json.dumps(dict(status="STARTED",variables=f.nv,clauses=len(f.clauses),
                          projection=row)),flush=True)
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(budget)
        result=sat.solve_limited()
        if result is None:
            return dict(status="UNKNOWN",**sat.accum_stats())
        if result:
            return dict(status="SAT_checked",path=read_path(sat.get_model(),9,221,end),
                        **sat.accum_stats())
        cnf,proof=prefix.with_suffix(".cnf"),prefix.with_suffix(".drat")
        f.to_file(str(cnf))
        proof.write_text("\n".join(sat.get_proof())+"\n")
        check=subprocess.run([checker,str(cnf),str(proof)],capture_output=True,check=True)
        assert b"s VERIFIED" in check.stdout
        return dict(status="UNSAT_DRAT_verified",proof=str(proof),**sat.accum_stats())


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("projections",type=Path)
    parser.add_argument("prefix",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--budget",type=int,default=400000)
    args=parser.parse_args()
    for line in args.projections.read_text().splitlines():
        row=json.loads(line)
        if row["counts"]==[9,9,9] and row["status"]=="FEASIBLE_RELAXATION":
            print(json.dumps(run(row,args.budget,args.prefix,args.checker)),flush=True)
            break
    else:
        raise ValueError("no 9,9,9 projection available")
