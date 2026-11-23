"""Search for six-dimensional forest caps using the proved Q5 constraints."""

import argparse
from itertools import combinations
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195, Minicard

from q5_certified_edge_capacity import lift, replay
from q6_star_interfaces import check
from q9_221_native_cardinality import cnf_replay_formula
from q9_q4_population import q4_populations
from q9_short_cycle_clauses import add_small_cycles
from verify_q9_free_dimension_cuts import deg, parts


def build(population, edge_minimum):
    # Every candidate has an edge. An automorphism maps it to {0,1}.
    formula=CNF(from_clauses=[[1],[2]])
    pool=IDPool(start_from=65)
    physical=[]
    for u in range(64):
        neighbors=[u^(1<<i) for i in range(6)]
        formula.extend([-u-1,*(-v-1 for v in trio)] for trio in combinations(neighbors,3))
        for v in neighbors:
            if u<v:
                edge=pool.id()
                physical.append((u,v,edge))
                formula.extend([[-edge,u+1],[-edge,v+1],[edge,-u-1,-v-1]])
    points=list(range(1,65))
    edges=[e for _,_,e in physical]
    limits=[([-v for v in points],64-population),([-e for e in edges],len(edges)-edge_minimum)]
    limits.extend((face,8) for face in q4_populations(6))
    lift(6,physical,formula,limits)
    add_small_cycles(formula,6,4)
    return formula,limits


def cycle_clause(loop):
    points=set(loop)
    assert points and len(points)==len(loop) and all(0<=v<64 for v in points)
    assert len(parts(points,6))==1 and all(deg(points,u,6)==2 for u in points)
    return [-v-1 for v in loop]


def trial(population,edges,budget,checker,out):
    formula,limits=build(population,edges)
    cuts=[]
    fields=dict(population=population,edges=edges)
    print(json.dumps(dict(status="STARTED",**fields,clauses=len(formula.clauses),budget=budget)),flush=True)
    with Minicard(bootstrap_with=formula) as solver:
        for row,k in limits:
            solver.add_atmost(row,k)
        while (left:=budget-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(left)
            answer=solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                cnf=cnf_replay_formula(formula,limits)
                with Cadical195(bootstrap_with=cnf,with_proof=True) as certifier:
                    if certifier.solve() is not False:
                        raise AssertionError("Native UNSAT failed to reproduce")
                    proof="\n".join(certifier.get_proof() or ["0"])+"\n"
                check(cnf,proof,checker)
                with out.open("x") as fp:
                    fp.write(json.dumps(dict(**fields,cycles=cuts,proof=proof))+"\n")
                return dict(status="Q6_CAP_PROOF_CHECKED",**fields,cycle_cuts=len(cuts))
            selected={v-1 for v in solver.get_model() if 1<=v<=64}
            cycles=[sorted(c) for c in parts(selected,6) if all(deg(selected,u,6)==2 for u in c)]
            if not cycles:
                assert len(selected)>=population and sum(deg(selected,u,6) for u in selected)//2>=edges
                assert all(deg(selected,u,6)<=2 for u in selected)
                return dict(status="FOREST_WITNESS_CHECKED",**fields,points=sorted(selected))
            for loop in cycles:
                cuts.append(loop)
                clause=cycle_clause(loop)
                formula.append(clause)
                solver.add_clause(clause)
        return dict(status="UNKNOWN",**fields,conflicts=solver.accum_stats()["conflicts"],cycles=len(cuts))


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("output",type=Path)
    parser.add_argument("q5_evidence",type=Path)
    parser.add_argument("checker")
    parser.add_argument("population",type=int)
    parser.add_argument("edges",type=int)
    parser.add_argument("--budget",type=int,default=200000)
    parser.add_argument("--replay",action="store_true")
    args=parser.parse_args()
    replay(args.q5_evidence,args.checker)
    if args.replay:
        rec=json.loads(args.output.read_text())
        assert (rec["population"],rec["edges"])==(args.population,args.edges)
        formula,limits=build(args.population,args.edges)
        formula.extend(cycle_clause(loop) for loop in rec["cycles"])
        check(cnf_replay_formula(formula,limits),rec["proof"],args.checker)
        print(json.dumps(dict(status="Q6_CAP_REPLAY_VERIFIED",population=args.population,edges=args.edges)))
    else:
        print(json.dumps(trial(args.population,args.edges,args.budget,args.checker,args.output)),flush=True)
