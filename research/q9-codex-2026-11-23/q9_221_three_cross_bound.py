"""Exact 221-edge Q9 search with a direction used three times."""
import argparse
import json
import subprocess
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import build, read_path
from q9_free_pair_cuts import add_pair_cuts


def encode(first_edges, direction_cuts):
    if first_edges not in (108, 109, 110):
        raise ValueError("first layer must have 108, 109 or 110 edges")
    f, end = build(9, 221, 9)
    pool = IDPool(start_from=f.nv + 1)
    # Coordinate 8 is the chosen three-crossing direction.
    for layer, count in enumerate((first_edges + 2, 220 - first_edges)):
        f.extend(CardEnc.equals(
            [v + 1 for v in range(256 * layer, 256 * (layer + 1))],
            count, vpool=pool, encoding=EncType.totalizer,
        ).clauses)
    crossings = []
    for v in range(256):
        edge = pool.id()
        crossings.append(edge)
        f.extend([[-edge, v + 1], [-edge, v + 257], [edge, -v - 1, -v - 257]])
    f.extend(CardEnc.equals(crossings, 3, vpool=pool, encoding=EncType.totalizer).clauses)
    if direction_cuts:
        add_pair_cuts(f, f.nv, minimum=17)
    return f, end


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("first_edges", type=int, choices=[108, 109, 110])
    parser.add_argument("budget", type=int)
    parser.add_argument("--checker", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pair-cuts", action="store_true")
    args = parser.parse_args()
    f, end = encode(args.first_edges, args.pair_cuts)
    result = dict(layer_edges=[args.first_edges, 218 - args.first_edges],
                  pair_cuts=args.pair_cuts, budget=args.budget,
                  clauses=len(f.clauses), variables=f.nv)
    print(json.dumps(dict(status="STARTED", **result)), flush=True)
    with Cadical195(bootstrap_with=f, with_proof=True) as solver:
        solver.conf_budget(args.budget)
        answer = solver.solve_limited()
        result.update(solver.accum_stats())
        if answer is None:
            result["status"] = "UNKNOWN"
        elif answer:
            path = read_path(solver.get_model(), 9, 221, end)
            assert sum((a ^ b) == 256 for a, b in zip(path, path[1:])) == 3
            result.update(status="SAT_checked", path=path)
        else:
            cnf = args.output.with_suffix(".cnf")
            drat = args.output.with_suffix(".drat")
            f.to_file(str(cnf))
            drat.write_text("\n".join(solver.get_proof()) + "\n")
            check = subprocess.run([args.checker, str(cnf), str(drat)],
                                   capture_output=True, check=True)
            assert b"s VERIFIED" in check.stdout
            result.update(status="UNSAT_DRAT_verified", cnf=str(cnf), drat=str(drat))
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
