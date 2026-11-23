"""Check whether two 25-edge Q6 forests can share a selected column."""
import argparse
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from itertools import combinations
from verify_q9_free_dimension_cuts import parts, deg


def base():
    f=CNF(from_clauses=[[1],[65]])
    pool=IDPool(start_from=129)
    for v in range(128):
        neighbors=[(v^(1<<d))+1 for d in range(7)]
        for bad in combinations(neighbors,3):
            f.append([-v-1,*(-w for w in bad)])
        for a,b in combinations(range(7),2):
            mask=(1<<a)|(1<<b)
            if not v&mask:
                f.append([-v-1,-(v^(1<<a))-1,-(v^(1<<b))-1,-(v^mask)-1])
    for layer in range(2):
        vertices=list(range(1+64*layer,65+64*layer))
        f.extend(CardEnc.atmost(vertices,32,vpool=pool,encoding=EncType.seqcounter).clauses)
        edges=[]
        for v in vertices:
            for axis in range(6):
                w=((v-1)^(1<<axis))+1
                if v>=w:
                    continue
                e=pool.id()
                f.extend([[-e,v],[-e,w],[e,-v,-w]])
                edges.append(e)
        f.extend(CardEnc.atleast(edges,25,vpool=pool,encoding=EncType.totalizer).clauses)
    return f


def search(budget, output, checker):
    f=base()
    print(json.dumps(dict(status="STARTED",variables=f.nv,clauses=len(f.clauses))),flush=True)
    cuts=[]
    spent=0
    while spent<budget:
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            sat.conf_budget(budget-spent)
            answer=sat.solve_limited()
            spent+=sat.accum_stats()["conflicts"]
            if answer is None:
                break
            if answer is False:
                cnf=output.with_suffix(".cnf")
                trace=output.with_suffix(".drat")
                f.to_file(str(cnf))
                trace.write_text("\n".join(sat.get_proof())+"\n")
                verified=subprocess.run([checker,str(cnf),str(trace)],capture_output=True,check=True)
                assert b"s VERIFIED" in verified.stdout
                return dict(status="UNSAT_DRAT_verified",cuts=cuts,conflicts=spent)
            points={v-1 for v in sat.get_model() if 1<=v<=128}
        cycles=[sorted(c) for c in parts(points,7) if all(deg(c,v,7)==2 for v in c)]
        if not cycles:
            return dict(status="SAT_checked",points=sorted(points),conflicts=spent,
                        layer_edges=[sum(deg(c,v,7) for v in c)//2
                                     for c in ({v for v in points if v<64},{v for v in points if v>=64})])
        for c in cycles:
            f.append([-v-1 for v in c])
            cuts.append(c)
    return dict(status="UNKNOWN",cuts=cuts,conflicts=spent)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("budget",type=int)
    parser.add_argument("output",type=Path)
    parser.add_argument("checker")
    print(json.dumps(search(**vars(parser.parse_args()))),flush=True)
