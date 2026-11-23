"""Exhaustive Q5 test of the parity-graph relaxation for an induced 14-edge path."""
from collections import Counter
from itertools import combinations
import json


def bit_indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def components(mask, graph):
    while mask:
        frontier = mask & -mask
        part = 0
        while frontier:
            bit = frontier & -frontier
            frontier ^= bit
            part |= bit
            frontier |= graph[bit.bit_length() - 1] & ~part
        yield part
        mask ^= part


def matchings(mask, graph):
    if mask == 0:
        yield ()
        return
    vertex = next(bit_indices(mask))
    for partner in bit_indices(mask & graph[vertex]):
        edge = (1 << vertex) | (1 << partner)
        for rest in matchings(mask ^ edge, graph):
            yield (edge,) + rest


def main():
    rows = [sum(1 << (z ^ direction) for direction in (0, 1, 2, 4, 8))
            for z in range(16)]
    totals = Counter()
    outcomes = Counter()
    for points in combinations(range(16), 8):
        totals["sets"] += 1
        mask = sum(1 << x for x in points)
        graph = [0] * 16
        hosts = 0
        for row in rows:
            neighbors = row & mask
            if neighbors.bit_count() == 2:
                hosts += 1
                a, b = bit_indices(neighbors)
                graph[a] |= 1 << b
                graph[b] |= 1 << a
        if hosts < 7:
            continue
        totals["seven_hosts"] += 1
        if sum(g.bit_count() for g in graph) < 14:
            continue
        totals["seven_distinct_edges"] += 1
        if len(list(components(mask, graph))) != 1:
            continue
        totals["connected"] += 1
        leaves = sum(1 << x for x in points if graph[x].bit_count() == 1)
        if leaves.bit_count() > 2:
            continue
        totals["at_most_two_leaves"] += 1
        low = sum(1 << x for x in points if graph[x].bit_count() <= 2)
        overload = sum(max(0, (graph[x] & low).bit_count() - 2) for x in points)
        if overload > 2 - leaves.bit_count():
            continue
        totals["low_degree_cut"] += 1
        perfect = list(matchings(mask, graph))
        shapes = set()
        for x, y in combinations(points, 2):
            ends = (1 << x) | (1 << y)
            if leaves & ~ends:
                continue
            for alternate in matchings(mask ^ ends, graph):
                for first in perfect:
                    if set(first).intersection(alternate):
                        continue
                    union = [0] * 16
                    for edge in first + alternate:
                        a, b = bit_indices(edge)
                        union[a] |= 1 << b
                        union[b] |= 1 << a
                    shape = []
                    for part in components(mask, union):
                        kind = "path" if ends & part else "cycle"
                        shape.append(kind + str(part.bit_count()))
                    shapes.add("+".join(sorted(shape)))
        outcomes[";".join(sorted(shapes))] += 1
    print(json.dumps({"sets_after_each_cut": totals, "shapes_per_set": outcomes}, indent=2))
    assert totals["sets"] == 12870
    assert outcomes == {"cycle4+path4": 480}


if __name__ == "__main__":
    main()
