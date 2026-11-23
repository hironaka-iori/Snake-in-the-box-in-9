"""Partition the 221-edge search with a 17-crossing pair by four Q7 layers."""
import argparse
import json
import subprocess
from itertools import product
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_direction_frequency import build
from q9_endpoint_distance_bound import read_path
from q9_square_census import add_popcount

SIDES = ((0,1),(0,2),(1,3),(2,3))


def patterns():
    for sizes in product((4,5), repeat=4):
        if sizes[0]+sizes[3] != 9 or sizes[1]+sizes[2] != 9:
            continue
        a,b,c,d = (2*n-(i in (0,1)) for i,n in enumerate(sizes))
        for first in range(min(a,b)+1):
            edges = (first,a-first,b-first,c-a+first)
            if min(edges) < 0 or edges[2]+edges[3] != d:
                continue
            if sum(x>0 for x in edges) < 3:
                continue
            odd = edges[0]+edges[3]
            if 3 <= odd <= 13 and odd%2 == 1:
                yield sizes, edges


def build_interfaces(distance, profiles=()):
    f, end, counts = build(9, 221, distance, tight_pair=True)
    if profiles:
        from q9_221_use_verified_profiles import add_triple_floors, exclude_profiles

        exclude_profiles(f, counts, distance, profiles)
        add_triple_floors(f, counts, distance, profiles)
    pool = IDPool(start_from=f.nv+1)
    vertices = [[] for _ in range(4)]
    inside = [[] for _ in range(4)]
    crossing = [[] for _ in SIDES]

    def layer(u):
        return (u&1)|(2*(u>>distance&1))

    for u in range(512):
        group = layer(u)
        vertices[group].append(u+1)
        for axis in range(9):
            v = u | (1<<axis)
            if u == v:
                continue
            other = layer(v)
            bond = pool.id()
            f.extend([[-bond,u+1],[-bond,v+1],[bond,-u-1,-v-1]])
            if group == other:
                inside[group].append(bond)
            else:
                crossing[SIDES.index((group,other))].append(bond)

    def count(values):
        return add_popcount(f,pool,[values])

    def fixed(bits, value):
        assert value >> len(bits) == 0
        return [bit if value>>i&1 else -bit for i,bit in enumerate(bits)]

    for values in inside:
        f.extend([[x] for x in fixed(count(values), 51)])
    size_bits = [count(values) for values in vertices]
    edge_bits = [count(values) for values in crossing]
    rows = []
    for sizes, edges in patterns():
        assumptions = [lit for bits,n in zip(size_bits,sizes) for lit in fixed(bits,51+n)]
        assumptions.extend(lit for bits,n in zip(edge_bits,edges) for lit in fixed(bits,n))
        rows.append((sizes,edges,assumptions))
    assert len(rows) == 24
    return f,end,rows


def certify(f, assumptions, target, checker):
    with Cadical195(bootstrap_with=f,with_proof=True) as solver:
        for lit in assumptions:
            solver.add_clause([lit])
        if solver.solve() is not False:
            return 'UNSAT_REPLAY_FAILED'
        proof = solver.get_proof()
    cnf_path, proof_path = target.with_suffix('.cnf'), target.with_suffix('.drat')
    f.extend([[x] for x in assumptions])
    try:
        f.to_file(str(cnf_path))
    finally:
        del f.clauses[-len(assumptions):]
    proof_path.write_text('\n'.join(proof)+'\n')
    checked = subprocess.run([checker,str(cnf_path),str(proof_path)],capture_output=True)
    target.with_suffix('.check.log').write_bytes(checked.stdout+checked.stderr)
    return ('UNSAT_DRAT_VERIFIED' if checked.returncode==0 and
            b's VERIFIED' in checked.stdout else 'UNSAT_REPLAY_FAILED')


def search(distance, budget, stem, checker, profiles=()):
    f,end,rows = build_interfaces(distance, profiles)
    print(json.dumps(dict(status='STARTED',distance=distance,
                          clauses=len(f.clauses),profiles=len(rows),
                          verified_frequency_cuts=len(profiles),budget_per_case=budget)),flush=True)
    with Cadical195(bootstrap_with=f) as solver:
        for i,(sizes,edges,assumptions) in enumerate(rows):
            before=solver.accum_stats()['conflicts']
            solver.conf_budget(budget)
            answer=solver.solve_limited(assumptions=assumptions)
            conflicts=solver.accum_stats()['conflicts']-before
            result=dict(distance=distance,index=i,layer_components=sizes,crossings=edges,
                        conflicts=conflicts,status='UNKNOWN')
            target=stem.with_name(stem.name+f'_case{i:02d}')
            if answer is False:
                result['status']=certify(f,assumptions,target,checker)
            elif answer:
                path=read_path(solver.get_model(),9,221,end)
                target.with_suffix('.path').write_text(' '.join(map(str,path))+'\n')
                result['status']='SAT_PATH_VERIFIED'
            print(json.dumps(result),flush=True)
            if answer:
                break


if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('distance',type=int,choices=(3,5,7))
    p.add_argument('budget',type=int)
    p.add_argument('stem',type=Path)
    p.add_argument('checker')
    p.add_argument("--ledger",type=Path)
    args=p.parse_args()
    profiles=json.loads(args.ledger.read_text()) if args.ledger else ()
    search(args.distance,args.budget,args.stem,args.checker,profiles)

