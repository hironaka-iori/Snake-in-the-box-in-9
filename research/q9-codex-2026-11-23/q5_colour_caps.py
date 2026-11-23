"""Produce, replay, and lift Q5 forest colour/edge bounds."""

import argparse
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q5_certified_edge_capacity import cycle_clause, local_model
from q6_star_interfaces import check
from q9_direction_frequency import append_upper_bound
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from verify_q9_free_dimension_cuts import deg, parts


CAPS = (
    (1, 14, -1), (1, 15, -1), (2, 13, -1), (2, 14, -1), (3, 13, -1),
    (5, 10, 9), (5, 11, -1), (6, 9, 11), (6, 10, 10), (7, 9, -1),
)
TILINGS = ((0, 1, 2, 3, 4), (2, 3, 5, 7, 8), (0, 1, 4, 6, 7))


def proposal(black, white, cap):
    f = local_model(black + white, cap + 1)
    pool = IDPool(start_from=f.nv + 1)
    for colour, count in enumerate((black, white)):
        layer = [u + 1 for u in range(32) if u.bit_count() % 2 == colour]
        f.extend(CardEnc.equals(layer, count, vpool=pool, encoding=EncType.cardnetwrk))
    return f


def certify(case, checker):
    f = proposal(*case)
    cycles = []
    with Cadical195(bootstrap_with=f, with_proof=True) as solver:
        while solver.solve():
            selected = {lit - 1 for lit in solver.get_model() if 1 <= lit <= 32}
            found = [sorted(c) for c in parts(selected, 5)
                     if all(deg(selected, u, 5) == 2 for u in c)]
            if not found:
                raise ValueError(f"Counterexample to {case}: {sorted(selected)}")
            for cycle in found:
                clause = cycle_clause(cycle)
                f.append(clause)
                solver.add_clause(clause)
                cycles.append(cycle)
        proof = "\n".join(solver.get_proof() or ["0"]) + "\n"
    check(f, proof, checker)
    return dict(case=case, cycles=cycles, proof=proof)


def replay(path, checker):
    rows = json.loads(path.read_text())
    assert tuple(tuple(row["case"]) for row in rows) == CAPS
    for row in rows:
        f = proposal(*row["case"])
        f.extend(cycle_clause(cycle) for cycle in row["cycles"])
        check(f, row["proof"], checker)
    return rows


def lift(f, physical, tilings=TILINGS, dim=9):
    pool = IDPool(start_from=f.nv + 1)
    edges_by_axis = [[] for _ in range(dim)]
    for u, v, lit in physical:
        edges_by_axis[(u ^ v).bit_length() - 1].append((u, lit))
    for axes in tilings:
        free = sum(1 << axis for axis in axes)
        for root in range(1 << dim):
            if root & free:
                continue
            populations = [add_popcount(f, pool, [[u + 1 for u in range(1 << dim)
                            if u & ~free == root and u.bit_count() % 2 == colour]])
                           for colour in (0, 1)]
            edges = add_popcount(f, pool, [[lit for axis in axes for u, lit in edges_by_axis[axis]
                                           if u & ~free == root]])
            for black, white, cap in CAPS:
                for left, right in ((black, white), (white, black)):
                    claims = value_literals(populations[0], left) + value_literals(populations[1], right)
                    guard = [-lit for lit in claims]
                    if cap < 0:
                        f.append(guard)
                    else:
                        append_upper_bound(f, edges, cap, guard)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("certify", "replay"))
    parser.add_argument("artifact", type=Path)
    parser.add_argument("checker")
    args = parser.parse_args()
    if args.mode == "certify":
        rows = [certify(case, args.checker) for case in CAPS]
        with args.artifact.open("x") as out:
            out.write(json.dumps(rows) + "\n")
    else:
        rows = replay(args.artifact, args.checker)
    print(json.dumps(dict(status="VERIFIED", checker_cases=len(rows), mode=args.mode)), flush=True)
