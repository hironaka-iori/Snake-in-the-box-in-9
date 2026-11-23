"""Screen Q9 projection orbits with independently replayed Q6 seam rules."""

import argparse
from collections import defaultdict
from itertools import permutations
import json
from pathlib import Path

from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list


def verified_rules(manifests):
    rules = defaultdict(set)
    for manifest in manifests:
        report = json.loads(manifest.read_text())
        assert report["status"] == "VERIFIED"
        rows = {tuple(row) for row in report["rules"]}
        assert len(rows) == len(report["rules"])
        assert report["anchor_certificates"] == sum(len(anchor_list(c, e)) for e, c, *_ in rows)
        for e, c, neighbor_edges, neighbor_vertices, crossings in rows:
            assert neighbor_edges > 0 and neighbor_vertices > neighbor_edges and crossings > 0
            rules[e, c].add((neighbor_edges, neighbor_vertices, crossings))
    return rules


def violates(profile, rules):
    edges, components, crossings = profile
    for (u, v), r in zip(BONDS, crossings):
        if not r:
            continue
        for a, b in ((u, v), (v, u)):
            n = edges[b] + components[b]
            if any(edges[b] >= eb and n >= nb and r >= rb
                   for eb, nb, rb in rules.get((edges[a], components[a]), ())):
                return True
    return False


def verified_star_rules(manifests, terminal=False):
    rules = defaultdict(set)
    for manifest in manifests:
        report = json.loads(manifest.read_text())
        assert report["status"] == "VERIFIED" and report.get("terminal_anchor", False) == terminal
        keys = set()
        for e, c, leaves in report["rules"]:
            shape = tuple(tuple(leaf) for leaf in leaves)
            assert 2 <= len(shape) <= 3
            assert all(eb > 0 and nb > eb and r > 0 for eb, nb, r in shape)
            key = e, c, shape
            assert key not in keys
            keys.add(key)
            rules[e, c].add(shape)
        assert report["anchor_certificates"] == sum(len(anchor_list(c, e)) for e, c, _ in keys)
    return rules


def violates_star(profile, rules, terminal=False):
    if not rules:
        return False
    edges, components, crossings = profile
    incident = [[] for _ in edges]
    for (u, v), r in zip(BONDS, crossings):
        if r:
            incident[u].append((edges[v], edges[v] + components[v], r))
            incident[v].append((edges[u], edges[u] + components[u], r))
    for u, (e, c, neighbors) in enumerate(zip(edges, components, incident)):
        if terminal and u not in (0, 7):
            continue
        for shape in rules.get((e, c), ()):
            for order in permutations(neighbors, len(shape)):
                if all(x >= y for actual, threshold in zip(order, shape)
                       for x, y in zip(actual, threshold)):
                    return True
    return False


def run(prefix, baseline, destination, manifests):
    def read(label):
        source = prefix.with_name(f"{prefix.name}_{label}.json")
        return json.loads(source.read_text())

    joint = []
    terminals = []
    pairs = []
    for path in manifests:
        report = json.loads(path.read_text())
        found = report["rules"]
        if report.get("terminal_anchor", False):
            terminals.append(path)
        elif found and len(found[0]) == 3:
            joint.append(path)
        else:
            pairs.append(path)
    rules = verified_rules(pairs)
    stars = verified_star_rules(joint)
    terminal_stars = verified_star_rules(terminals, terminal=True)
    old = read(baseline)
    profiles = read("profiles")["representatives"]
    assert old["status"] == "VERIFIED"
    if terminal_stars:
        assert all(n % 2 for n in old["counts"])
    initial = old["indices"]
    assert len(initial) == len(set(initial))
    assert old["initial"] == old["excluded_by_local"] + len(initial) == len(profiles)
    assert all(0 <= i < len(profiles) for i in initial)
    survivors = [i for i in initial
                 if not violates(profiles[i], rules) and not violates_star(profiles[i], stars)
                 and not violates_star(profiles[i], terminal_stars, terminal=True)]
    removed = len(initial) - len(survivors)
    excluded = old["excluded_by_local"] + removed
    report = dict(status="VERIFIED", counts=old["counts"], initial=old["initial"],
                  excluded_by_local=excluded, indices=survivors, new_exclusions=removed,
                  prior_screen=f"{prefix.name}_{baseline}.json",
                  certificate_libraries=[str(path) for path in manifests])
    with destination.open("x") as output:
        json.dump(report, output)
        output.write("\n")
    print(json.dumps(dict(counts=old["counts"], excluded=removed, remaining=len(survivors))))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prefix", type=Path)
    parser.add_argument("baseline")
    parser.add_argument("destination", type=Path)
    parser.add_argument("manifests", nargs="+", type=Path)
    args = parser.parse_args()
    run(args.prefix, args.baseline, args.destination, args.manifests)
