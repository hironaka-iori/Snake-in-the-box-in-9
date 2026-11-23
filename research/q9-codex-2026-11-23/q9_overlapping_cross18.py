"""Enforce overlapping Q7 interface profiles for 221-edge Q9 searches."""
import argparse
import json
from itertools import combinations
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_cross18_interface_profiles import patterns
from q9_direction_frequency import build
from q9_endpoint_distance_bound import read_path
from q9_square_census import add_popcount
from q9_tight_interface_search import SIDES, certify


def value_literals(bits, value):
    assert 0 <= value < 1 << len(bits)
    return [bit if value >> i & 1 else -bit for i,bit in enumerate(bits)]


def add_pair_interface(f, pool, all_bonds, counts, a, b, odd):
    count_sum = add_popcount(f,pool,[list(column) for column in zip(counts[a],counts[b])])
    active = pool.id()
    count_equals_18 = value_literals(count_sum,18)
    f.extend([[-active,lit] for lit in count_equals_18])
    f.append([active,*(-lit for lit in count_equals_18)])

    inside = [[] for _ in range(4)]
    sizes = [[] for _ in range(4)]
    sides = [[] for _ in range(4)]

    def layer(u):
        return (u>>a&1)+2*(u>>b&1)

    partition = [layer(u) for u in range(512)]
    for u,group in enumerate(partition):
        sizes[group].append(u+1)
    for u,v,bond in all_bonds:
        left,right = partition[u],partition[v]
        if left == right:
            inside[left].append(bond)
        else:
            sides[SIDES.index((left,right))].append(bond)

    internal_bits = [add_popcount(f,pool,[inputs]) for inputs in inside]
    size_bits = [add_popcount(f,pool,[inputs]) for inputs in sizes]
    cross_bits = [add_popcount(f,pool,[inputs]) for inputs in sides]
    choices = []
    for edges,components,crossings in patterns(odd):
        choice = pool.id()
        choices.append(choice)
        for fields,values in ((internal_bits,edges),
                              (size_bits,[e+c for e,c in zip(edges,components)]),
                              (cross_bits,crossings)):
            for bits,value in zip(fields,values):
                f.extend([[-choice,lit] for lit in value_literals(bits,value)])
    f.append([-active,*choices])
    return active


def model(distance, subset):
    f,end,counts = build(9,221,distance)
    pool = IDPool(start_from=f.nv+1)
    all_bonds = []
    for u in range(512):
        for axis in range(9):
            v = u | (1<<axis)
            if u != v:
                bond = pool.id()
                f.extend([[-bond,u+1],[-bond,v+1],[bond,-u-1,-v-1]])
                all_bonds.append((u,v,bond))

    active = {}
    for block in (range(distance),range(distance,9)):
        axes = tuple(block)[:subset]
        for a,b in combinations(axes,2):
            active[a,b] = add_pair_interface(f,pool,all_bonds,counts,a,b,a<distance)
    return f,end,active


def search(distance, budget, checker, stem, subset):
    f,end,active = model(distance,subset)
    minimum_indicators = [active[0,1]]
    if distance < 8:
        minimum_indicators.append(active[distance,distance+1])
    header = dict(distance=distance,interfaces=len(active),budget=budget,clauses=len(f.clauses))
    print(json.dumps(dict(status='STARTED',**header)),flush=True)
    with Cadical195(bootstrap_with=f) as solver:
        for i,active_minimum in enumerate(minimum_indicators):
            before = solver.accum_stats()['conflicts']
            assumptions = [active_minimum]
            solver.conf_budget(budget)
            result = solver.solve_limited(assumptions=assumptions)
            status = 'UNKNOWN'
            target = stem.with_name(stem.name+('_odd' if i==0 else '_even'))
            if result is False:
                status = certify(f,assumptions,target,checker)
            elif result:
                path = read_path(solver.get_model(),9,221,end)
                target.with_suffix('.path').write_text(' '.join(map(str,path))+'\n')
                status = 'SAT_PATH_VERIFIED'
            print(json.dumps(dict(status=status,odd=(i==0),
                                  conflicts=solver.accum_stats()['conflicts']-before,**header)),flush=True)
            if result:
                break


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('distance',type=int,choices=(3,5,7,9))
    parser.add_argument('budget',type=int)
    parser.add_argument('stem',type=Path)
    parser.add_argument('checker')
    parser.add_argument('--subset',type=int,choices=(2,3,4),default=3)
    args = parser.parse_args()
    search(args.distance,args.budget,args.checker,args.stem,args.subset)

