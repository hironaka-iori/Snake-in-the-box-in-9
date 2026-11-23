"""Check for a dense Q8 forest avoiding the closed neighborhoods of two distance-three terminals."""

import argparse
import gzip
from itertools import combinations
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_direction_frequency import append_upper_bound
from q9_endpoint_lex import add_endpoint_lex
from q9_overlapping_cross18 import value_literals
from q9_q4_forest_diagram import forest_masks
from q9_q4_population import add_q4_population, q4_populations
from q9_square_census import add_popcount
from verify_q9_free_dimension_cuts import deg, parts


def forbidden_vertices():
    return {u for u in range(256) if min(u.bit_count(), (u^7).bit_count()) <= 1}


def add_hole_aware_caps(f, pool, forbidden, allowed):
    forests = sorted(forest_masks(),key=int.bit_count,reverse=True)
    bounds = {}
    for face in q4_populations(8):
        holes = sum(1<<i for i,v in enumerate(face) if v-1 in forbidden)
        if holes not in bounds:
            bounds[holes] = next(m.bit_count() for m in forests if not m&holes)
        physical = [v for v in face if v-1 in allowed]
        if bounds[holes] < len(physical):
            append_upper_bound(f,add_popcount(f,pool,[physical]),bounds[holes])
    black = [v+1 for v in sorted(allowed) if not v.bit_count()%2]
    # An odd 107-vertex forest with two path components has imbalance one.
    for encoder, value in ((CardEnc.atleast,53),(CardEnc.atmost,54)):
        f.extend(encoder(black,value,vpool=pool,encoding=EncType.totalizer))


def make_formula(hole_aware=False):
    forbidden = forbidden_vertices()
    allowed = set(range(256))-forbidden
    f = CNF(from_clauses=[[-u-1] for u in sorted(forbidden)])
    pool = IDPool(start_from=257)
    bonds = []
    for u in sorted(allowed):
        neighbors = sorted({u^(1<<axis) for axis in range(8)} & allowed)
        for bad in combinations(neighbors, 3):
            f.append([-u-1, *(-v-1 for v in bad)])
        for v in neighbors:
            if u < v:
                edge = pool.id()
                f.extend([[-edge,u+1],[-edge,v+1],[edge,-u-1,-v-1]])
                bonds.append(edge)
        for a, b in combinations(range(8), 2):
            mask = (1<<a)|(1<<b)
            square = {u,u^(1<<a),u^(1<<b),u^mask}
            if not u&mask and square <= allowed:
                f.append([-v-1 for v in sorted(square)])
    for block,total in (([u+1 for u in sorted(allowed)],107),(bonds,105)):
        if hole_aware:
            bits=add_popcount(f,pool,[block])
            f.extend([lit] for lit in value_literals(bits,total))
        else:
            f.extend(CardEnc.equals(block,total,vpool=pool,encoding=EncType.totalizer))
    if hole_aware:
        add_hole_aware_caps(f,pool,forbidden,allowed)
    else:
        add_q4_population(f,pool,8)
    add_endpoint_lex(f,8,3)
    return f


def ring_clause(ring):
    points = set(ring)
    assert len(points)==len(ring) and all(0<=u<256 for u in points)
    assert len(parts(points,8))==1 and all(deg(points,u,8)==2 for u in points)
    return [-u-1 for u in ring]


def search(f, budget, checker):
    cycles=[]
    with Cadical195(bootstrap_with=f,with_proof=True) as solver:
        while (remaining:=budget-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(remaining)
            answer=solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof="\n".join(solver.get_proof() or ["0"])+"\n"
                check(f,proof,checker)
                return dict(status="UNSAT_DRAT_VERIFIED", proof=proof, cycles=cycles)
            points={u-1 for u in solver.get_model() if 1<=u<=256}
            assert len(points)==107 and not points & forbidden_vertices()
            degrees={u:deg(points,u,8) for u in points}
            assert max(degrees.values())<=2 and sum(degrees.values())==210
            components=parts(points,8)
            rings=[sorted(group) for group in components if all(degrees[u]==2 for u in group)]
            if not rings:
                assert len(components)==2
                return dict(status="SAT_FOREST_VERIFIED", points=sorted(points))
            for ring in rings:
                clause=ring_clause(ring)
                f.append(clause)
                solver.add_clause(clause)
                cycles.append(ring)
        return dict(status="UNKNOWN", conflicts=solver.accum_stats()["conflicts"], cycles=len(cycles))


def run(args):
    formula=make_formula(args.hole_aware)
    if args.replay:
        with gzip.open(args.archive,"rt") as file:
            row=json.load(file)
        assert row["status"]=="UNSAT_DRAT_VERIFIED" and row.get("hole_aware",False)==args.hole_aware
        formula.extend(ring_clause(ring) for ring in row["cycles"])
        check(formula,row["proof"],args.checker)
        print(json.dumps(dict(status="VERIFIED",population=107,components=2,
                              terminal_distance=3)),flush=True)
        return
    print(json.dumps(dict(status="STARTED",clauses=len(formula.clauses),
                          budget=args.budget,forbidden=len(forbidden_vertices()),hole_aware=args.hole_aware)),flush=True)
    result=search(formula,args.budget,args.checker)
    result["hole_aware"]=args.hole_aware
    with gzip.open(args.archive,"xt") as file:
        json.dump(result,file)
    print(json.dumps({k:v for k,v in result.items() if k not in ("proof","points")}),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--replay",action="store_true")
    parser.add_argument("--hole-aware",action="store_true")
    parser.add_argument("--budget",type=int,default=1100000)
    run(parser.parse_args())
