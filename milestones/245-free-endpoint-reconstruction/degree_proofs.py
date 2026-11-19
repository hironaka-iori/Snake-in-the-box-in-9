"""Construct exclusion trees for the cases decided by the external solver."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import csv
import json
import zipfile

HERE = Path(__file__).resolve().parent


def augmented_edges(selected, minority):
    selected = set(selected)
    pairs = set()
    endpoints = set() if minority else set(selected)
    for label in range(512):
        neighbours = sorted(selected.intersection(label ^ (1 << i) for i in range(9)))
        if len(neighbours) == 2:
            pairs.add(tuple(neighbours))
        elif len(neighbours) == 1 and minority:
            endpoints.add(neighbours[0])
    return sorted(selected | {512}), sorted(pairs | {(v, 512) for v in endpoints})


def exclusion_tree(points, edges):
    incident = {v: 0 for v in points}
    for i, (a, b) in enumerate(edges):
        incident[a] |= 1 << i
        incident[b] |= 1 << i
    statistics = Counter()

    def visit(allowed, fixed):
        statistics["nodes"] += 1
        if statistics["nodes"] > 150000:
            raise RuntimeError("Branch budget reached")
        while True:
            before = allowed, fixed
            for v, neighbourhood in incident.items():
                available = allowed & neighbourhood
                used = fixed & neighbourhood
                if available.bit_count() < 2:
                    return ["insufficient", v]
                if used.bit_count() > 2:
                    return ["excess", v]
                if available.bit_count() == 2:
                    fixed |= available
                elif used.bit_count() == 2:
                    allowed &= ~(available ^ used)
            if before == (allowed, fixed):
                break

        def component(start, edge_mask):
            seen = {start}
            queue = [start]
            for v in queue:
                choices = incident[v] & edge_mask
                while choices:
                    bit = choices & -choices
                    choices ^= bit
                    a, b = edges[bit.bit_length() - 1]
                    other = a if b == v else b
                    if other not in seen:
                        seen.add(other)
                        queue.append(other)
            return seen

        if len(component(points[0], allowed)) < len(points):
            return ["disconnected", points[0]]
        left = set(points)
        while left:
            start = min(left)
            group = component(start, fixed)
            left -= group
            if all((fixed & incident[v]).bit_count() == 2 for v in group):
                if len(group) == len(points):
                    raise ValueError("Connected two-factor exists")
                return ["proper_cycle", start]
        undecided = allowed ^ fixed
        v = min((v for v in points if incident[v] & undecided),
                key=lambda v: ((incident[v] & undecided).bit_count(), v))
        branch = incident[v] & undecided
        bit = branch & -branch
        a, b = edges[bit.bit_length() - 1]
        statistics["branches"] += 1
        return [a, b, visit(allowed, fixed | bit), visit(allowed ^ bit, fixed)]

    return visit((1 << len(edges)) - 1, 0), statistics


def main():
    results = json.loads((HERE / "results.json").read_bytes())
    with zipfile.ZipFile(HERE.parents[1] / "work/record_snakes.csv.zip") as archive:
        raw = archive.read("snakes_dim9_190.csv")
    if sha256(raw).hexdigest() != results["input_sha256"]:
        raise ValueError("Parent collection differs")
    parents = [list(map(int, r["vertices"].split())) for r in csv.DictReader(raw.decode().splitlines())]
    records = []
    totals = Counter()
    for family in results["families"]:
        minority = family["minority"]
        if len(family["native_inputs"]) != family["unique_outcomes"]["native_exclusion"]:
            raise ValueError("Incomplete solver-case list")
        for case in family["native_inputs"]:
            selected = parents[case["parent"]][int(minority)::2] + [case["add"]]
            points, edges = augmented_edges(selected, minority)
            tree, stats = exclusion_tree(points, edges)
            totals.update(stats)
            records.append(dict(**case, minority=minority, edges=len(edges), tree=tree))
    out = dict(input_sha256=results["input_sha256"], code_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
               cases=len(records), totals=totals, records=records)
    (HERE / "degree-proofs.json").write_text(json.dumps(out, separators=(",", ":")) + "\n",
                                              encoding="utf-8", newline="\n")
    print("graphs", len(records), "proof-tree totals", dict(totals))


if __name__ == "__main__":
    main()
