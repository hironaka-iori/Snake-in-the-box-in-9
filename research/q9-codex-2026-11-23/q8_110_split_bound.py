"""Bounded searches for the eight possible Q7 splits of a 110-edge Q8 forest."""
import argparse
import itertools
import json
import subprocess
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from verify_q9_free_dimension_cuts import edge7, parts, deg


def cases():
    # With 110 edges some direction has at most floor(110/8) crossings.
    for r in range(14):
        for a in range((r+1)//2, 2+r-(r+1)//2+1):
            b=2+r-a
            for x in range(edge7(a)+1):
                y=110-r-x
                if (a,x) > (b,y) or not 0 <= y <= edge7(b):
                    continue
                if r and max(x,y)==52 and min(x,y)>=51:
                    continue
                if r>=4 and ((x==52 and y>=50 and y+b>=54) or
                             (y==52 and x>=50 and x+a>=54)):
                    continue
                yield r,a,b,x,y


def encode(r,a,b,x,y):
    f=CNF()
    pool=IDPool(start_from=257)
    def count(lits, n, encoder=CardEnc.equals):
        f.extend(encoder(lits,n,vpool=pool,encoding=EncType.totalizer).clauses)
    axes=[[] for _ in range(8)]
    layers=[[],[]]
    for v in range(256):
        neighbors=[(v^(1<<d))+1 for d in range(8)]
        for triple in itertools.combinations(neighbors,3):
            f.append([-v-1,*(-w for w in triple)])
        for i,w in enumerate(neighbors):
            if w<=v+1:
                continue
            e=pool.id()
            f.extend([[-e,v+1],[-e,w],[e,-v-1,-w]])
            axes[i].append(e)
            if i<7:
                layers[v>>7].append(e)
        for i,j in itertools.combinations(range(8),2):
            mask=(1<<i)|(1<<j)
            if not v&mask:
                f.append([-v-1,-(v^(1<<i))-1,-(v^(1<<j))-1,-(v^mask)-1])
    count(list(range(1,129)),x+a)
    count(list(range(129,257)),y+b)
    count(layers[0],x)
    count(layers[1],y)
    count(axes[7],r)
    for bonds in axes[:7]:
        count(bonds,r,CardEnc.atleast)
    return f


def run(case,budget,out,checker):
    f=encode(*case)
    print(json.dumps(dict(case=case,status="STARTED",clauses=len(f.clauses))),flush=True)
    cuts=[]
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        while (remaining:=budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(remaining)
            answer=sat.solve_limited()
            if answer is None:
                break
            if not answer:
                name=out/"q8_110_split_{}".format("_".join(map(str,case)))
                cnf=name.with_suffix(".cnf")
                trace=name.with_suffix(".drat")
                f.to_file(str(cnf))
                with Cadical195(bootstrap_with=f,with_proof=True) as certifier:
                    assert certifier.solve() is False
                    trace.write_text("\n".join(certifier.get_proof())+"\n")
                check=subprocess.run([checker,str(cnf),str(trace)],capture_output=True,check=True)
                assert b"s VERIFIED" in check.stdout
                return dict(status="UNSAT_DRAT_verified", proof=str(trace), cycles=cuts)
            points={v-1 for v in sat.get_model() if 1<=v<=256}
            cycles=[sorted(c) for c in parts(points,8) if all(deg(c,v,8)==2 for v in c)]
            if not cycles:
                assert len(points)==112 and len(parts(points,8))==2
                return dict(status="SAT_checked",points=sorted(points))
            for cycle in cycles:
                cl=[-v-1 for v in cycle]
                cuts.append(cycle)
                f.append(cl)
                sat.add_clause(cl)
        return dict(status="UNKNOWN",conflicts=sat.accum_stats()["conflicts"],
                    cycles=len(cuts))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("budget",type=int)
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    args=p.parse_args()
    for case in cases():
        print(json.dumps(dict(case=case,**run(case,args.budget,args.out,args.checker))),flush=True)
