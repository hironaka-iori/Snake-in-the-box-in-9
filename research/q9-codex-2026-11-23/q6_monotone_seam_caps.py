"""Certify joint lower bounds impossible across a seam of two Q6 layers."""

import argparse
from concurrent.futures import ProcessPoolExecutor
import gzip
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check, formula as star_formula
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def build(anchor, rule):
    _, _, edges, population, crossings = rule
    points = {u for u in range(64) if anchor >> u & 1}
    allowed = set(range(64)) - {u for u in points if deg(points, u, 6) == 2}
    f = star_formula(anchor, ((edges, None, crossings),))
    pool = IDPool(start_from=max(f.nv, 64) + 1)
    if population > len(allowed):
        f.append([])
    else:
        f.extend(CardEnc.atleast([u + 1 for u in sorted(allowed)], population,
                                 vpool=pool, encoding=EncType.cardnetwrk).clauses)
    return f, points, allowed


def cycle_clause(cycle, anchor):
    points = set(cycle)
    assert len(points) == len(cycle) and all(0 <= u < 128 for u in points)
    assert len(parts(points, 7)) == 1 and all(deg(points, u, 7) == 2 for u in points)
    assert {u for u in points if u < 64} <= anchor
    cut = [-u + 63 for u in cycle if u >= 64]
    assert cut
    return cut


def certify(anchor, rule, budget, checker):
    f, points, allowed = build(anchor, rule)
    cycles = []
    with Cadical195(bootstrap_with=f, with_proof=True) as sat:
        while (remaining := budget - sat.accum_stats()["conflicts"]) > 0:
            sat.conf_budget(remaining)
            answer = sat.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof = "\n".join(sat.get_proof() or ["0"]) + "\n"
                check(f, proof, checker)
                return dict(status="UNSAT_DRAT_VERIFIED", cycles=cycles, proof=proof)
            model = set(sat.get_model())
            selected = {v for v in allowed if v + 1 in model}
            full = points | {v + 64 for v in selected}
            assert len(selected) >= rule[3] and len(selected & points) >= rule[4]
            assert all(deg(full, v, 7) <= 2 for v in full)
            assert sum(deg(selected, v, 6) for v in selected) >= 2 * rule[2]
            rings = [sorted(group) for group in parts(full, 7)
                     if all(deg(group, v, 7) == 2 for v in group)]
            if not rings:
                return dict(status="SAT_FOREST_VERIFIED", points=sorted(full))
            for ring in rings:
                clause = cycle_clause(ring, points)
                f.append(clause)
                sat.add_clause(clause)
                cycles.append(ring)
    return dict(status="UNKNOWN")


def verify_case(job):
    rule, record, checker = job
    assert record["status"] == "UNSAT_DRAT_VERIFIED"
    f, fixed, _ = build(record["anchor"], rule)
    f.extend(cycle_clause(cycle, fixed) for cycle in record["cycles"])
    check(f, record["proof"], checker)


def run(args):
    if args.output is not None:
        rules = []
        checked = 0
        with gzip.open(args.archive, "rt") as archive:
            for line in archive:
                row = json.loads(line)
                rule = row["rule"]
                expected = set(anchor_list(rule[1], rule[0]))
                cases = row["cases"]
                assert expected and len(cases) == len(expected)
                assert {rec["anchor"] for rec in cases} == expected
                jobs = ((rule, rec, args.checker) for rec in cases)
                if args.jobs == 1:
                    for job in jobs:
                        verify_case(job)
                        checked += 1
                else:
                    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
                        for count, _ in enumerate(pool.map(verify_case, jobs, chunksize=8),1):
                            checked += 1
                            if count % 256 == 0:
                                print(json.dumps(dict(status="REPLAY_PROGRESS", rule=rule,
                                                      checked=count,total=len(cases))),flush=True)
                rules.append(rule)
        with args.output.open("x") as output:
            json.dump(dict(status="VERIFIED", rules=rules, anchor_certificates=checked), output)
        print(json.dumps(dict(status="VERIFIED", rules=len(rules),
                              anchor_certificates=checked)), flush=True)
        return

    with gzip.open(args.archive, "xt") as archive:
        for rule in args.rule:
            anchors = anchor_list(rule[1], rule[0])
            assert anchors
            cases = []
            for anchor in anchors:
                result = certify(anchor, rule, args.budget, args.checker)
                if result["status"] != "UNSAT_DRAT_VERIFIED":
                    print(json.dumps(dict(rule=rule, anchor=anchor, checked=len(cases),
                                          status=result["status"])), flush=True)
                    break
                cases.append(dict(anchor=anchor, **result))
            else:
                archive.write(json.dumps(dict(rule=rule, cases=cases)) + "\n")
                archive.flush()
                print(json.dumps(dict(rule=rule, checked=len(cases),
                                      status="ALL_ANCHORS_EXCLUDED")), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("archive", type=Path)
    parser.add_argument("checker")
    parser.add_argument("--rule", type=int, nargs=5, action="append")
    parser.add_argument("--budget", type=int, default=125000)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("Replay worker count must be positive.")
    if args.output is None and not args.rule:
        parser.error("Provide at least one rule to test.")
    run(args)
