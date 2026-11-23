"""Decide whether two Q7 forests with 51 edges each can share a Q8 interface."""
import argparse
import json
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q9_short_cycle_clauses import add_small_cycles


def build(contacts, components=None):
    f = CNF()
    pool = IDPool(start_from=257)
    inside = [[], []]
    cross = []
    for u in range(256):
        neighbors = [u ^ (1 << axis) for axis in range(8)]
        for triple in combinations(neighbors, 3):
            f.append([-u-1, *(-v-1 for v in triple)])
        for v in neighbors:
            if v <= u:
                continue
            edge = pool.id()
            f.extend([[-edge, u+1], [-edge, v+1], [edge, -u-1, -v-1]])
            (inside[u >> 7] if u ^ v < 128 else cross).append(edge)
    for layer in range(2):
        f.extend(CardEnc.equals(inside[layer], 51, vpool=pool, encoding=EncType.totalizer))
        vertices = list(range(128*layer+1, 128*layer+129))
        if components is None:
            f.extend(CardEnc.atleast(vertices, 55, vpool=pool, encoding=EncType.totalizer))
            f.extend(CardEnc.atmost(vertices, 56, vpool=pool, encoding=EncType.totalizer))
        else:
            f.extend(CardEnc.equals(vertices, 51 + components[layer], vpool=pool,
                                    encoding=EncType.totalizer))
    f.extend(CardEnc.atleast(cross, contacts, vpool=pool, encoding=EncType.totalizer))
    f.extend(CardEnc.atmost(cross, 9, vpool=pool, encoding=EncType.totalizer))
    # Translate one interface contact to the origin.
    f.extend([[1], [129]])
    add_small_cycles(f, 8, 3)
    return f


def inspect(points, minimum):
    assert all(0 <= u < 256 for u in points)
    adjacent = {u: {u ^ (1 << axis) for axis in range(8)} & points for u in points}
    assert max(map(len, adjacent.values())) <= 2
    counts = [0, 0]
    cross = 0
    for u, neighbors in adjacent.items():
        for v in neighbors:
            if v > u:
                if (u ^ v) == 128:
                    cross += 1
                else:
                    counts[u >> 7] += 1
    assert counts == [51, 51] and minimum <= cross <= 9
    sizes = [sum(u >> 7 == layer for u in points) for layer in range(2)]
    assert all(size in (55,56) for size in sizes)
    unseen = set(points)
    cycles = []
    components = []
    while unseen:
        pending = [unseen.pop()]
        component = []
        while pending:
            u = pending.pop()
            component.append(u)
            new = adjacent[u] & unseen
            unseen.difference_update(new)
            pending.extend(new)
        if all(len(adjacent[u]) == 2 for u in component):
            cycles.append(sorted(component))
        components.append(len(component))
    return cycles, dict(cross=cross, internal=counts, sizes=sizes,
                        component_sizes=sorted(components))


def search(minimum, budget, output, components=None, checker=None):
    f = build(minimum, components)
    print(json.dumps(dict(status='STARTED', contacts=minimum, variables=f.nv,
                          clauses=len(f.clauses), budget=budget, components=components)), flush=True)
    cuts = []
    with Cadical195(bootstrap_with=f) as sat:
        while (remaining := budget-sat.accum_stats()['conflicts']) > 0:
            sat.conf_budget(remaining)
            answer = sat.solve_limited()
            if answer is None:
                break
            if answer is False:
                status = "UNSAT_SOLVER"
                if checker:
                    from q9_tight_interface_search import certify

                    status = certify(f, [1], output, checker)
                record = dict(status=status, cycle_cuts=cuts)
                break
            points = {x-1 for x in sat.get_model() if 1 <= x <= 256}
            cycles, details = inspect(points, minimum)
            if not cycles:
                if components is not None:
                    assert details["sizes"] == [51 + count for count in components]
                record = dict(status='SAT_WITNESS_VERIFIED', points=sorted(points), **details)
                break
            for cycle in cycles:
                clause = [-u-1 for u in cycle]
                sat.add_clause(clause)
                if checker:
                    f.append(clause)
                cuts.append(cycle)
        else:
            answer = None
        if answer is None:
            record = dict(status='UNKNOWN', cycle_cuts=cuts)
        record.update(stats=sat.accum_stats(), contacts=minimum, components=components)
    output.write_text(json.dumps(record)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('points','cycle_cuts')}), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--contacts', type=int, default=5)
    p.add_argument('--budget', type=int, default=300000)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument("--components", type=int, nargs=2, choices=(4, 5))
    p.add_argument("--checker")
    args = p.parse_args()
    search(args.contacts, args.budget, args.out, args.components, args.checker)

