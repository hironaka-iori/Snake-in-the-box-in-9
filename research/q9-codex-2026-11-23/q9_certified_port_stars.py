"""Exclude projection patterns by joining verified Q6 port placements at a root."""

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

from q9_geometry_cut_library import orientations
from q9_join_interface_masks import Catalogue, degrees
from q9_three_tight_pairs import BONDS


def candidates(profiles, indices, banks):
    frequency = Counter()
    for index in indices:
        e, c, crossings = profiles[index]
        incident = [[] for _ in range(8)]
        for (u, v), count in zip(BONDS, crossings):
            if not count:
                continue
            uv = e[u], c[u], e[v], c[v], count
            if uv in banks:
                incident[u].append(uv[2:])
                incident[v].append((e[u], c[u], count))
        stars = set()
        for u, links in enumerate(incident):
            for size in (2, 3):
                for subset in combinations(sorted(links), size):
                    stars.add((e[u], c[u], subset))
        frequency.update(stars)
    return frequency


def incompatible_stars(entries, banks, limit):
    @lru_cache(maxsize=20000)
    def ports(key, root):
        return sorted({root & neighbor for neighbor in banks[key][root]})

    @lru_cache(maxsize=30000)
    def possible(edges, components, cases):
        keys = [(edges, components, *case) for case in cases]
        roots = set.intersection(*(set(banks[key]) for key in keys))
        for root in roots:
            one, two = degrees(root)
            options = [ports(key, root) for key in keys]
            for contact in product(*options):
                used, twice = 0, two
                for mask in contact:
                    if mask & twice:
                        break
                    twice |= mask & (used | one)
                    used |= mask
                else:
                    return True
        return False

    rejected = set()
    for star, hits in entries.most_common(limit):
        e, c, cases = star
        if any((e, c, pair) in rejected for pair in combinations(cases, 2)):
            continue
        if not possible(*star):
            rejected.add(star)
            yield star, hits


def write_patterns(rejected, output, table):
    patterns = []
    for (e, c, cases), hits in rejected:
        neighbors = [1 << i for i in range(len(cases))]
        faces = [(0, e, c)] + [(u, f, d) for u, (f, d, _) in zip(neighbors, cases)]
        links = [(0, u, r) for u, (_, _, r) in zip(neighbors, cases)]
        faces, links = min(orientations(faces, links))
        patterns.append(dict(faces=faces, links=links, catalogue=str(table),
                             root_star=[e, c, cases], candidate_hits=hits))
    with output.open("x") as file:
        file.write(json.dumps(dict(source_certificates=len(patterns), patterns=patterns)) + "\n")
    return len(patterns)


def run(table, prefix, audit_label, output, limit):
    def read(label):
        return json.loads(prefix.with_name(f"{prefix.name}_{label}.json").read_text())

    profiles = read("profiles")["representatives"]
    audit = read(audit_label)
    indices = audit["remaining"] if "remaining" in audit else audit["indices"]
    bank = Catalogue(table)
    entries = candidates(profiles, indices, bank.banks)
    print(json.dumps(dict(status="STARTED", profiles=len(indices), stars=len(entries))), flush=True)
    count = write_patterns(incompatible_stars(entries, bank.banks, limit), output, table)
    print(json.dumps(dict(status="VERIFIED_PORT_STARS", patterns=count)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("table", type=Path)
    parser.add_argument("prefix", type=Path)
    parser.add_argument("audit_label")
    parser.add_argument("output", type=Path)
    parser.add_argument("--limit", type=int, default=2500)
    args = parser.parse_args()
    run(args.table, args.prefix, args.audit_label, args.output, args.limit)
