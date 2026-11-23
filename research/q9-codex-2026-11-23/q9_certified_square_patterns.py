"""Search and independently replay four-layer Q2 obstructions."""

import argparse
from collections import Counter
from functools import lru_cache
import gzip
from itertools import islice, product
import json
from pathlib import Path

from q6_star_interfaces import check
from q9_certify_geometric_joins import make, trial
from q9_geometry_cut_library import orientations
from q9_join_interface_masks import Catalogue
from q9_three_tight_pairs import BONDS
from verify_q9_free_dimension_cuts import deg, parts


QUAD = ((0, 1), (2, 3), (0, 2), (1, 3))
INDEX = {bond: i for i, bond in enumerate(BONDS)}
FACES = []
for axis, side in product(range(3), range(2)):
    layers = tuple(u for u in range(8) if (u >> axis) & 1 == side)
    FACES.append((layers, tuple(INDEX[layers[u], layers[v]] for u, v in QUAD)))
PERMUTATIONS = []
for swap, origin in product(range(2), range(4)):
    mapped = tuple(((((u & 1) << 1) | (u >> 1)) if swap else u) ^ origin
                   for u in range(4))
    indices = tuple(QUAD.index(tuple(sorted((mapped[u], mapped[v])))) for u, v in QUAD)
    PERMUTATIONS.append((mapped, indices))


@lru_cache(maxsize=60000)
def canonical_square(layers, crossings):
    return min((tuple(layers[i] for i in vertices), tuple(crossings[i] for i in bonds))
               for vertices, bonds in PERMUTATIONS)


def collect(profiles, indices, bank):
    counts = Counter()
    representative = {}
    for i in indices:
        e, c, crossings = profiles[i]
        supported = [(e[u], c[u], e[v], c[v], k) in bank
                     for (u, v), k in zip(BONDS, crossings)]
        seen = set()
        for layers, slots in FACES:
            if sum(supported[j] for j in slots) < 3:
                continue
            key = canonical_square(tuple((e[u], c[u]) for u in layers),
                                   tuple(crossings[j] for j in slots))
            seen.add(key)
            representative.setdefault(key, (i, layers))
        counts.update(seen)
    return counts, representative


def shape(row, layers):
    e, c, crossings = row
    faces = [(v, e[v], c[v]) for v in sorted(layers)]
    links = [(u, v, k) for (u, v), k in zip(BONDS, crossings) if u in layers and v in layers]
    assert len(faces) == len(links) == 4
    return min(orientations(faces, links))


def search(profiles, audit, bank, args):
    counts, representatives = collect(profiles, audit["remaining"], bank.banks)
    print(json.dumps(dict(status="STARTED", candidates=len(counts),
                          tests=min(len(counts), args.limit))), flush=True)
    with gzip.open(args.archive, "xt") as output:
        for key, hits in counts.most_common(args.limit):
            i, layers = representatives[key]
            result = trial(profiles[i], set(layers), bank, args.domain_limit,
                           args.budget, args.checker)
            status = result["status"]
            if status == "UNSAT_DRAT_VERIFIED":
                row = dict(index=i, layers=layers, hits=hits, **result)
                output.write(json.dumps(row) + "\n")
                output.flush()
            print(json.dumps(dict(status=status, index=i, layers=layers,
                                  potential_hits=hits)), flush=True)


def replay(profiles, bank, args):
    patterns = {}
    checks = 0
    with gzip.open(args.archive, "rt") as source:
        rows = source if args.records is None else islice(source, args.records)
        for line in rows:
            record = json.loads(line)
            assert record["status"] == "UNSAT_DRAT_VERIFIED"
            row = profiles[record["index"]]
            layers = set(record["layers"])
            assert tuple(sorted(layers)) in {points for points, _ in FACES}
            formula, layouts = make(row, layers, bank, args.domain_limit)
            assert layouts == record["layouts"]
            for cycle in record["cycles"]:
                points = set(cycle)
                assert len(points) == len(cycle) and all(v >> 6 in layers for v in points)
                assert len(parts(points, 9)) == 1 and all(deg(points, v, 9) == 2 for v in points)
                formula.append([-v - 1 for v in cycle])
            check(formula, record["proof"], args.checker)
            faces, links = shape(row, layers)
            patterns.setdefault((faces, links), dict(faces=faces, links=links,
                                index=record["index"], catalogue=str(args.table)))
            checks += 1
    if args.records is not None:
        assert checks == args.records
    with args.output.open("x") as output:
        json.dump(dict(source_certificates=checks, patterns=list(patterns.values())), output)
    print(json.dumps(dict(status="VERIFIED", square_patterns=len(patterns),
                          checker_cases=checks)), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles", "audit", "table", "archive"):
        parser.add_argument(name, type=Path)
    parser.add_argument("checker")
    parser.add_argument("--limit", type=int, default=160)
    parser.add_argument("--budget", type=int, default=42000)
    parser.add_argument("--domain-limit", type=int, default=10000)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--records", type=int)
    args = parser.parse_args()
    if args.records is not None and (args.output is None or args.records < 1):
        parser.error("--records requires a replay output and a positive count")
    profiles = json.loads(args.profiles.read_text())["representatives"]
    bank = Catalogue(args.table)
    if args.output:
        replay(profiles, bank, args)
    else:
        search(profiles, json.loads(args.audit.read_text()), bank, args)
