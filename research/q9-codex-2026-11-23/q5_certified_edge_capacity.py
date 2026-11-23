"""Certify induced Q5 forest edge caps and build their Q9 lifts."""

import argparse
from itertools import combinations
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from verify_q9_free_dimension_cuts import deg, parts


CASES = ((0,14),(15,13))


def local_model(population, edges):
    formula = CNF()
    pool = IDPool(start_from=33)
    selected = list(range(1,33))
    physical = []
    for u in range(32):
        neighbours = [u^(1<<axis) for axis in range(5)]
        for a,b,c in combinations(neighbours,3):
            formula.append([-u-1,-a-1,-b-1,-c-1])
        for v in neighbours:
            if u<v:
                edge = pool.id()
                formula.extend([[-edge,u+1],[-edge,v+1],[edge,-u-1,-v-1]])
                physical.append(edge)
    formula.extend(CardEnc.atleast(selected,population,vpool=pool,encoding=EncType.cardnetwrk))
    formula.extend(CardEnc.atleast(physical,edges,vpool=pool,encoding=EncType.cardnetwrk))
    return formula


def cycle_clause(cycle):
    points=set(cycle)
    assert points and len(points)==len(cycle) and all(0<=v<32 for v in points)
    assert len(parts(points,5))==1 and all(deg(points,u,5)==2 for u in points)
    return [-v-1 for v in cycle]


def certify(population, edges, checker):
    formula=local_model(population,edges)
    cuts=[]
    with Cadical195(bootstrap_with=formula,with_proof=True) as solver:
        while solver.solve():
            vertices={lit-1 for lit in solver.get_model() if 1<=lit<=32}
            found=[sorted(g) for g in parts(vertices,5) if all(deg(vertices,u,5)==2 for u in g)]
            if not found:
                assert len(vertices)>=population
                assert sum(deg(vertices,u,5) for u in vertices)//2>=edges
                raise ValueError(f"Counterexample for {(population,edges)}: {sorted(vertices)}")
            for cycle in found:
                cuts.append(cycle)
                clause=cycle_clause(cycle)
                formula.append(clause)
                solver.add_clause(clause)
        proof="\n".join(solver.get_proof() or ["0"])+"\n"
    check(formula,proof,checker)
    return dict(population=population,edges=edges,cycles=cuts,proof=proof)


def replay(path, checker):
    data=json.loads(path.read_text())
    assert sorted((rec["population"],rec["edges"]) for rec in data)==list(CASES)
    for rec in data:
        formula=local_model(rec["population"],rec["edges"])
        formula.extend(cycle_clause(cycle) for cycle in rec["cycles"])
        check(formula,rec["proof"],checker)
    return data


def lift(dim, physical, formula, limits):
    assert dim>=5
    pool=IDPool(start_from=max(formula.nv,max(abs(lit) for bank,_ in limits for lit in bank))+1)
    banks={tuple(sorted((a,b))):lit for a,b,lit in physical}
    for axes in combinations(range(dim),5):
        free=sum(1<<a for a in axes)
        slices={}
        for u in range(1<<dim):
            root=u&~free
            points,edges=slices.setdefault(root,([],[]))
            points.append(u+1)
            for a in axes:
                v=u^(1<<a)
                if v>u:
                    edges.append(banks[u,v])
        for points,edges in slices.values():
            high = pool.id()
            copy = pool.id()
            formula.extend([[high,copy],[-high,-copy]])
            # n >= 15 forces high. n <= 16 follows from the two Q4 halves.
            limits.append((points+[-high,copy],16))
            limits.append((edges+[high],13))


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("mode",choices=("certify","replay"))
    parser.add_argument("evidence",type=Path)
    parser.add_argument("checker")
    args=parser.parse_args()
    if args.mode=="certify":
        data=[certify(n,e,args.checker) for n,e in CASES]
        with args.evidence.open("x") as fp:
            fp.write(json.dumps(data)+"\n")
    else:
        data=replay(args.evidence,args.checker)
    print(json.dumps(dict(status="Q5_EDGE_CAPS_VERIFIED",mode=args.mode,
                          cases=[dict(population=r["population"],edges=r["edges"],
                                      cycle_cuts=len(r["cycles"])) for r in data])))
