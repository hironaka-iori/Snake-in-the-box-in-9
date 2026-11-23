"""Certify simultaneous lower thresholds at multiple faces adjacent to a Q6 anchor."""

import argparse
from collections import Counter
import gzip
from itertools import combinations
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check, formula as star_formula
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def layers(leaves):
    return [(1 << i) * 64 for i in range(len(leaves))]


def build(mask, leaves, terminal=False):
    fixed = {v for v in range(64) if mask >> v & 1}
    allowed = sorted(set(range(64)) - {v for v in fixed if deg(fixed, v, 6) == 2})
    f = star_formula(mask, [(edges, None, crossings) for edges, _, crossings in leaves])
    pool = IDPool(start_from=max(f.nv, 64 * len(leaves)) + 1)
    for side, (_, population, _) in enumerate(leaves):
        if population > len(allowed):
            f.append([])
        else:
            positions = [1 + 64 * side + v for v in allowed]
            f.extend(CardEnc.atleast(positions, population, vpool=pool,
                                     encoding=EncType.cardnetwrk).clauses)
    if terminal:
        endpoint_choices = []
        for v in sorted(fixed):
            internal_degree = deg(fixed, v, 6)
            if internal_degree == 2:
                continue
            endpoint = pool.id()
            endpoint_choices.append(endpoint)
            incoming = [1 + 64 * side + v for side in range(len(leaves))]
            for used in combinations(incoming, 2 - internal_degree):
                f.append([-endpoint, *(-port for port in used)])
        f.append(endpoint_choices)
    return f, fixed, allowed


def cycle_clause(cycle, fixed, offsets):
    points = set(cycle)
    assert len(points) == len(cycle)
    assert points <= fixed | {offset + v for offset in offsets for v in range(64)}
    dim = 6 + len(offsets)
    assert len(parts(points, dim)) == 1
    assert all(deg(points, v, dim) == 2 for v in points)
    sides = {offset: side for side, offset in enumerate(offsets)}
    cut = [-(1 + 64 * sides[v - v % 64] + v % 64) for v in sorted(points - fixed)]
    assert cut
    return cut


def prove(mask, leaves, budget, checker, terminal=False):
    f, fixed, allowed = build(mask, leaves, terminal)
    offsets = layers(leaves)
    dim = 6 + len(leaves)
    cycles = []
    with Cadical195(bootstrap_with=f, with_proof=True) as solver:
        while (left := budget - solver.accum_stats()["conflicts"]) > 0:
            solver.conf_budget(left)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof = "\n".join(solver.get_proof() or ["0"]) + "\n"
                check(f, proof, checker)
                return dict(status="UNSAT_DRAT_VERIFIED", proof=proof, cycles=cycles)
            model = set(solver.get_model())
            full = set(fixed)
            for side, ((edges, population, crossings), offset) in enumerate(zip(leaves, offsets)):
                face = {v for v in allowed if 1 + 64 * side + v in model}
                assert len(face) >= population and len(face & fixed) >= crossings
                assert sum(deg(face, v, 6) for v in face) >= 2 * edges
                full.update(offset + v for v in face)
            assert all(deg(full, v, dim) <= 2 for v in full)
            rings = [sorted(group) for group in parts(full, dim)
                     if all(deg(group, v, dim) == 2 for v in group)]
            if not rings:
                return dict(status="SAT_FOREST_VERIFIED")
            for ring in rings:
                clause = cycle_clause(ring, fixed, offsets)
                f.append(clause)
                solver.add_clause(clause)
                cycles.append(ring)
    return dict(status="UNKNOWN")


def candidates(summary, anchor_edges, anchor_components, terminal=False):
    data = json.loads(summary.read_text())
    frequencies = Counter()
    for case in data["cases"]:
        if not case["remaining"]:
            continue
        source = summary.parent / case["source"]
        audit = json.loads(source.read_text())
        prefix = source.name.removesuffix("_partial_coverage_audit.json")
        rows = json.loads((summary.parent / f"{prefix}_profiles.json").read_text())["representatives"]
        for i in audit["remaining"]:
            edges, components, crossings = rows[i]
            incident = [[] for _ in edges]
            for (u, v), count in zip(BONDS, crossings):
                if count:
                    incident[u].append((edges[v], edges[v] + components[v], count))
                    incident[v].append((edges[u], edges[u] + components[u], count))
            keys = set()
            for u, (e, c, neighbors) in enumerate(zip(edges, components, incident)):
                if terminal and u not in (0, 7):
                    continue
                if e in anchor_edges and c in anchor_components:
                    for size in range(2, len(neighbors) + 1):
                        keys.update((e, c, tuple(sorted(choice))) for choice in combinations(neighbors, size))
            frequencies.update(keys)
    return frequencies


def run(summary, archive, checker, limit, budget, anchor_edges, anchor_components, terminal=False):
    score = candidates(summary, anchor_edges, anchor_components, terminal)
    families = {(e, c): anchor_list(c, e) for e, c in {(e, c) for e, c, _ in score}}
    eligible = [key for key in score if families[key[:2]]]
    order = sorted(eligible, key=lambda key: -score[key] / len(families[key[:2]]) ** .65)
    print(json.dumps(dict(status="STARTED", candidates=len(order),
                          unavailable_anchor_keys=len(score)-len(order))), flush=True)
    with gzip.open(archive, "xt") as out:
        for e, c, leaves in order[:limit]:
            key = e, c, leaves
            anchors = families[e, c]
            assert anchors
            cases = []
            for mask in anchors:
                result = prove(mask, leaves, budget, checker, terminal)
                if result["status"] != "UNSAT_DRAT_VERIFIED":
                    print(json.dumps(dict(key=key, hits=score[key], status=result["status"],
                                          checked=len(cases))), flush=True)
                    break
                cases.append(dict(mask=mask, **result))
            else:
                out.write(json.dumps(dict(key=key, cases=cases, terminal_anchor=terminal)) + "\n")
                out.flush()
                print(json.dumps(dict(key=key, hits=score[key], status="ALL_ANCHORS_EXCLUDED",
                                      checked=len(cases))), flush=True)


def replay(archive, checker, output, terminal=False):
    rules = []
    checked = 0
    with gzip.open(archive, "rt") as source:
        for line in source:
            row = json.loads(line)
            assert row.get("terminal_anchor", False) == terminal
            e, c, leaves = row["key"]
            assert 2 <= len(leaves) <= 3
            expected = set(anchor_list(c, e))
            cases = row["cases"]
            assert expected and len(cases) == len(expected)
            assert {case["mask"] for case in cases} == expected
            for case in cases:
                assert case["status"] == "UNSAT_DRAT_VERIFIED"
                f, fixed, _ = build(case["mask"], leaves, terminal)
                f.extend(cycle_clause(ring, fixed, layers(leaves)) for ring in case["cycles"])
                check(f, case["proof"], checker)
                checked += 1
            rules.append(row["key"])
    with output.open("x") as out:
        json.dump(dict(status="VERIFIED", rules=rules, anchor_certificates=checked, terminal_anchor=terminal), out)
    print(json.dumps(dict(status="VERIFIED", rules=len(rules), anchor_certificates=checked)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("checker")
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--summary", type=Path)
    action.add_argument("--output", type=Path)
    parser.add_argument("--anchor-edges", type=int, nargs="+", choices=(24,25,26), default=(25,26))
    parser.add_argument("--anchor-components", type=int, nargs="+", choices=range(1,9), default=range(1,9))
    parser.add_argument("--terminal-anchor", action="store_true")
    parser.add_argument("--limit", type=int, default=24)
    parser.add_argument("--budget", type=int, default=40000)
    args = parser.parse_args()
    if args.summary:
        run(args.summary, args.archive, args.checker, args.limit, args.budget, args.anchor_edges, args.anchor_components, args.terminal_anchor)
    else:
        replay(args.archive, args.checker, args.output, args.terminal_anchor)
