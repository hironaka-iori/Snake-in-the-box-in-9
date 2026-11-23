"""Verify an integer upper bound on the vertex count of a free second arm.

Only Python's standard library is needed. Each vertex chooses its selected
incident directions (or absence). Each affine face chooses its intersection
with the path. A matching vertex and face contribute opposite integer weights.
The second endpoint has its own cancelling weight. Maximizing each group
independently therefore gives an upper bound.
"""

import argparse
from collections import defaultdict
from itertools import combinations
import json


def incident_choices(v, root, parity, free):
    neighbors = [1 << d for d in range(8) if v ^ (1 << d) in free]
    if v != root:
        yield None
        yield from (a | b for a, b in combinations(neighbors, 2))
    if v == root or (v ^ root).bit_count() % 2 == parity:
        yield from neighbors


def is_forest(points, directions):
    seen = set()
    for v in points:
        if v in seen:
            continue
        stack = [v]
        seen.add(v)
        vertices = 0
        degree_sum = 0
        while stack:
            u = stack.pop()
            vertices += 1
            for d in directions:
                w = u ^ d
                if w in points:
                    degree_sum += 1
                    if w not in seen:
                        seen.add(w)
                        stack.append(w)
        if degree_sum >= 2 * vertices:
            return False
    return True


def verify(record):
    c = record["certificate"]
    arm = c["arm"]
    scale = c["scale"]
    assert type(scale) is int and scale > 0 and len(arm) >= 2
    assert len(arm) == len(set(arm)) and all(0 <= v < 256 for v in arm)
    assert all(
        ((arm[j] ^ arm[i]).bit_count() == 1) == (j == i + 1)
        for j in range(len(arm))
        for i in range(j)
    )
    free = set(range(256)).difference(arm[1:])
    root = arm[0]
    parity = c["end_parity"]
    assert parity in (0, 1)
    assert record["lower_edges"] == len(arm) - 1
    total_edges = record.get("total_edges", record.get("actual_q9_edges", 192))
    target = total_edges + 1 - len(arm)
    assert target == record["target_vertices"] and parity == (target - 1) % 2
    fee = c["end_weight"]
    assert type(fee) is int
    choices = {v: list(incident_choices(v, root, parity, free)) for v in free}
    weights = {}
    valid_directions = []
    for axes in c["directions"]:
        assert len(axes) == len(set(axes)) and all(0 <= d < 8 for d in axes)
        directions = [1 << d for d in axes]
        assert sum(directions) not in [sum(r) for r in valid_directions]
        valid_directions.append(directions)
    axisdict = {sum(ds): ds for ds in valid_directions}
    for f, v, local, value in c["matching_weights"]:
        ds = axisdict[f]
        assert 0 <= local < (1 << len(ds)) and v in free and type(value) is int
        inside = sum(d for j, d in enumerate(ds) if local >> j & 1)
        assert (f, v, inside) not in weights
        weights[f, v, inside] = value
    parity_fee = c.get("parity_weight", 0)
    assert type(parity_fee) is int
    bound = fee + parity_fee * int(parity == 0)
    for v, options in choices.items():

        def value(z):
            if z is None:
                return 0
            return (
                scale
                - parity_fee * (1 if (v ^ root).bit_count() % 2 == 0 else -1)
                - (fee if v != root and z.bit_count() == 1 else 0)
                + sum(weights.get((f, v, z & f), 0) for f in axisdict)
            )

        bound += max(map(value, options))
    for f, directions in axisdict.items():
        for base in range(256):
            if base & f:
                continue
            points = sorted(v for v in free if v & ~f == base)
            if not points:
                continue
            states = {v: {z & f for z in choices[v] if z is not None} for v in points}
            best = None
            for mask in range(1 << len(points)):
                picked = {v for j, v in enumerate(points) if mask >> j & 1}
                if root in points and root not in picked:
                    continue
                degrees = {
                    v: sum(d for d in directions if v ^ d in picked) for v in picked
                }
                if any(z not in states[v] for v, z in degrees.items()):
                    continue
                if not is_forest(picked, directions):
                    continue
                score = -sum(weights.get((f, v, z), 0) for v, z in degrees.items())
                best = score if best is None else max(best, score)
            assert best is not None
            bound += best
    assert bound == c["integer_numerator"] == record["integer_numerator"]
    assert bound // scale == record["vertices_upper"]
    if "partner_witness" in record:
        partner = record["partner_witness"]
        assert root == partner[0] and all(0 <= v < 256 for v in partner)
        assert (len(partner) - 1) % 2 == parity
        full = arm[::-1] + [v + 256 for v in partner]
        assert len(set(full)) == len(full) == record["actual_q9_edges"] + 1
        assert all(((v ^ full[j]).bit_count() == 1) == (j == i + 1)
                   for i, v in enumerate(full) for j in range(i + 1, len(full)))
        assert len(partner) <= bound // scale
    return bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("jsonl", nargs="+")
    args = parser.parse_args()
    for filename in args.jsonl:
        for line in open(filename):
            record = json.loads(line)
            bound = verify(record)
            print(
                record["index"],
                record["lower_edges"],
                bound,
                record["certificate"]["scale"],
                record["vertices_upper"],
                flush=True,
            )
