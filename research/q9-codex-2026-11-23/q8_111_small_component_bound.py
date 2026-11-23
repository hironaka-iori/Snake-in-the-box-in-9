"""Test Q8 forests of 111 vertices with at most three path components."""

import argparse
import gzip
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q5_colour_caps import lift, replay as replay_colour_caps
from q6_star_interfaces import check
from q8_110_split_bound import encode
from q9_q4_population import add_q4_population
from verify_q9_free_dimension_cuts import deg, edge7, parts


POPULATION = 111
TILINGS = ((0, 1, 2, 3, 4), (2, 3, 5, 6, 7))


def splits(components):
    edges = POPULATION - components
    for r in range(edges // 8 + 1):
        minimum = (r + 1) // 2
        for a in range(minimum, components + r - minimum + 1):
            b = components + r - a
            for x in range(edge7(a) + 1):
                y = edges - r - x
                if (a, x) > (b, y) or not 0 <= y <= edge7(b):
                    continue
                if r and max(x, y) == 52 and min(x, y) >= 51:
                    continue
                if r >= 4 and ((x == 52 and y >= 50 and y + b >= 54)
                               or (y == 52 and x >= 50 and x + a >= 54)):
                    continue
                yield r, a, b, x, y


def formula(case, components):
    result = encode(*case)
    pool = IDPool(start_from=result.nv + 1)
    even = [u + 1 for u in range(256) if u.bit_count() % 2 == 0]
    lower, upper = (POPULATION - components + 1) // 2, (POPULATION + components) // 2
    result.extend(CardEnc.atleast(even, lower, vpool=pool, encoding=EncType.cardnetwrk).clauses)
    result.extend(CardEnc.atmost(even, upper, vpool=pool, encoding=EncType.cardnetwrk).clauses)
    add_q4_population(result, pool, 8)
    physical = []
    for u in range(256):
        for axis in range(8):
            v = u | (1 << axis)
            if v != u:
                bond = pool.id()
                result.extend([[-bond, u + 1], [-bond, v + 1], [bond, -u - 1, -v - 1]])
                physical.append((u, v, bond))
    lift(result, physical, tilings=TILINGS, dim=8)
    return result


def cycle_clause(cycle):
    points = set(cycle)
    assert len(points) == len(cycle) and all(0 <= v < 256 for v in points)
    assert len(parts(points, 8)) == 1 and all(deg(points, v, 8) == 2 for v in points)
    return [-v - 1 for v in cycle]


def solve(case, components, budget, checker):
    f = formula(case, components)
    cycles = []
    with Cadical195(bootstrap_with=f, with_proof=True) as solver:
        while (remaining := budget - solver.accum_stats()["conflicts"]) > 0:
            solver.conf_budget(remaining)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof = "\n".join(solver.get_proof() or ["0"]) + "\n"
                check(f, proof, checker)
                return dict(status="UNSAT_DRAT_VERIFIED", cycles=cycles, proof=proof)
            points = {v - 1 for v in solver.get_model() if 1 <= v <= 256}
            groups = parts(points, 8)
            closed = [sorted(c) for c in groups if all(deg(c, v, 8) == 2 for v in c)]
            if not closed:
                assert len(points) == POPULATION and len(groups) == components
                assert all(deg(points, v, 8) <= 2 for v in points)
                return dict(status="SAT_FOREST_VERIFIED", points=sorted(points))
            for cycle in closed:
                clause = cycle_clause(cycle)
                f.append(clause)
                solver.add_clause(clause)
                cycles.append(cycle)
        return dict(status="UNKNOWN", conflicts=solver.accum_stats()["conflicts"])


def run(args):
    replay_colour_caps(args.colour_caps, args.checker)
    universe = set(splits(args.components))
    if args.replay:
        seen = set()
        with gzip.open(args.archive, "rt") as source:
            for line in source:
                row = json.loads(line)
                case = tuple(row["case"])
                assert case in universe and case not in seen
                if row["status"] != "UNSAT_DRAT_VERIFIED":
                    continue
                f = formula(case, args.components)
                f.extend(cycle_clause(cycle) for cycle in row["cycles"])
                check(f, row["proof"], args.checker)
                seen.add(case)
        print(json.dumps(dict(status="COVERAGE_AUDITED", components=args.components,
                              total=len(universe), excluded=len(seen),
                              remaining=sorted(universe-seen))), flush=True)
        return
    with gzip.open(args.archive, "xt") as out:
        for case in sorted(universe)[:args.limit]:
            result = solve(case, args.components, args.budget, args.checker)
            out.write(json.dumps(dict(case=case, **result)) + "\n")
            out.flush()
            print(json.dumps(dict(case=case, status=result["status"])), flush=True)
            if result["status"] == "SAT_FOREST_VERIFIED":
                break


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("components", type=int, choices=(2, 3))
    parser.add_argument("archive", type=Path)
    parser.add_argument("colour_caps", type=Path)
    parser.add_argument("checker")
    parser.add_argument("--limit", type=int, default=100)
    parser.add_argument("--budget", type=int, default=700000)
    parser.add_argument("--replay", action="store_true")
    run(parser.parse_args())
