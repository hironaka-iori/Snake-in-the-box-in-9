"""Validate two-layer signatures used by the three-direction projection."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from verify_q9_free_dimension_cuts import parts, deg


def signatures(path):
    count={}
    for line in path.read_text().splitlines():
        row=json.loads(line)
        if row["status"]!="FEASIBLE_RELAXATION":
            continue
        faces=list(zip(row["edges"],row["components"]))
        interfaces=[(v,v^(1<<axis)) for axis in range(3)
                    for v in range(8) if not v>>axis&1]
        for (a,b),r in zip(interfaces,row["crossings"]):
            if r:
                key=(*sorted((faces[a],faces[b]),reverse=True),r)
                count[key]=count.get(key,0)+1
    return sorted(count,key=lambda key:(-count[key],-key[0][0]-key[1][0],-key[2],key))


def formula(key, anchor=None):
    a,b,r=key
    f=CNF(from_clauses=[[1],[65]] if anchor is None else
          [[v+1 if anchor>>v&1 else -v-1] for v in range(64)])
    pool=IDPool(start_from=129)
    def equality(lits,number):
        f.extend(CardEnc.equals(lits,number,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    layer_edges=[[],[]]
    crossings=[]
    for v in range(128):
        neighbors=[(v^(1<<d))+1 for d in range(7)]
        for bad in combinations(neighbors,3):
            f.append([-v-1,*(-w for w in bad)])
        for d,w in enumerate(neighbors):
            if w<=v+1:
                continue
            edge=pool.id()
            f.extend([[-edge,v+1],[-edge,w],[edge,-v-1,-w]])
            (crossings if d==6 else layer_edges[v>>6]).append(edge)
        for i,j in combinations(range(7),2):
            u,w=1<<i,1<<j
            if not v&(u|w):
                f.append([-v-1,-(v^u)-1,-(v^w)-1,-(v^u^w)-1])
    for i,(e,c) in enumerate((a,b)):
        equality(list(range(64*i+1,64*i+65)),e+c)
        equality(layer_edges[i],e)
    equality(crossings,r)
    return f


def run(key,budget,out,checker,anchor=None):
    f=formula(key,anchor)
    spent=0
    cuts=[]
    while spent<budget:
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            sat.conf_budget(budget-spent)
            result=sat.solve_limited()
            spent+=sat.accum_stats()["conflicts"]
            if result is None:
                break
            if not result:
                a,b,r=key
                name=out/("local_q6_"+"_".join(map(str,(*a,*b,r))))
                if anchor is not None:
                    name=name.with_name(name.name+f"_{anchor:016x}")
                cnf,trace=name.with_suffix(".cnf"),name.with_suffix(".drat")
                f.to_file(str(cnf))
                trace.write_text("\n".join(sat.get_proof())+"\n")
                check=subprocess.run([checker,str(cnf),str(trace)],check=True,capture_output=True)
                assert b"s VERIFIED" in check.stdout
                return dict(status="UNSAT_DRAT_verified",conflicts=spent,cycles=cuts,trace=str(trace))
            points={v-1 for v in sat.get_model() if 1<=v<=128}
        cycles=[sorted(c) for c in parts(points,7) if all(deg(c,v,7)==2 for v in c)]
        if not cycles:
            layers=[{v%64 for v in points if v>>6==i} for i in (0,1)]
            for s,(e,c) in zip(layers,key[:2]):
                assert len(s)==e+c and len(parts(s,6))==c
                assert sum(deg(s,v,6) for v in s)==2*e
            assert len(layers[0]&layers[1])==key[2]
            return dict(status="SAT_checked",points=sorted(points),conflicts=spent)
        for c in cycles:
            f.append([-v-1 for v in c])
            cuts.append(c)
    return dict(status="UNKNOWN",conflicts=spent,cycles=cuts)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("profiles",type=Path)
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    p.add_argument("--budget",type=int,default=20000)
    p.add_argument("--max-cases",type=int,default=30)
    a=p.parse_args()
    for key in signatures(a.profiles)[:a.max_cases]:
        print(json.dumps(dict(key=key,status="STARTED")),flush=True)
        print(json.dumps(dict(key=key,**run(key,a.budget,a.out,a.checker))),flush=True)
