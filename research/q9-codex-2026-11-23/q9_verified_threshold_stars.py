"""Prove threshold rules shared by many Q6 projection profiles."""

import argparse
from collections import Counter
import gzip
from itertools import combinations
import json
from pathlib import Path

from q6_star_interfaces import check, formula, search
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list


def candidates(profiles, indices):
    score = Counter()
    for i in indices:
        edges, components, crossings = profiles[i]
        neighbors = [[] for _ in range(8)]
        for (a, b), r in zip(BONDS, crossings):
            if r:
                neighbors[a].append((edges[b], None, r))
                neighbors[b].append((edges[a], None, r))
        rules = set()
        for u, (e, c) in enumerate(zip(edges, components)):
            if e not in (25, 26):
                continue
            for size in (2, 3):
                rules.update((e, c, tuple(sorted(leaves)))
                             for leaves in combinations(neighbors[u], size))
        score.update(rules)
    return score


def search_profiles(args):
    rows = json.loads(args.profiles.read_text())["representatives"]
    audit = json.loads(args.audit.read_text())
    selected = candidates(rows, audit["remaining"])
    print(json.dumps(dict(status="STARTED", candidates=len(selected),
                          tests=min(len(selected), args.limit))), flush=True)
    with gzip.open(args.archive, "xt") as file:
        for key, score in selected.most_common(args.limit):
            e, c, _ = key
            anchors = anchor_list(c, e)
            assert anchors
            result = search(key, anchors, args.checker, args.budget)
            status = result["status"]
            if status == "UNSAT_all_anchors_verified":
                file.write(json.dumps(result) + "\n")
                file.flush()
            print(json.dumps(dict(status=status, key=key, frequency=score,
                                  anchors=len(anchors))), flush=True)


def replay(args):
    rules = []
    checked = 0
    with gzip.open(args.archive, "rt") as file:
        for line in file:
            row = json.loads(line)
            e, c, leaves = row["key"]
            assert e in (25, 26) and len(leaves) in (2, 3)
            assert all(comp is None and r > 0 for _, comp, r in leaves)
            assert row["status"] == "UNSAT_all_anchors_verified"
            anchors = anchor_list(c, e)
            assert len(row["cases"]) == len(anchors)
            assert {int(case["anchor"], 16) for case in row["cases"]} == set(anchors)
            for case in row["cases"]:
                assert case["status"] == "UNSAT_DRAT_verified"
                check(formula(int(case["anchor"], 16), leaves), case["proof"], args.checker)
                checked += 1
            rules.append(row["key"])
    with args.output.open("x") as file:
        json.dump(dict(status="VERIFIED", anchor_certificates=checked, rules=rules), file)
    print(json.dumps(dict(status="VERIFIED", rules=len(rules), checked=checked)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles", "audit", "archive"):
        parser.add_argument(name, type=Path)
    parser.add_argument("checker")
    parser.add_argument("--limit", type=int, default=24)
    parser.add_argument("--budget", type=int, default=30000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.output is None:
        search_profiles(args)
    else:
        replay(args)
