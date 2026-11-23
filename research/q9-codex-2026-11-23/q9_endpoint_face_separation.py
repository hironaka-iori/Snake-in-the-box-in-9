"""Endpoint separation inside coordinate regions too small for the whole path."""

from itertools import combinations


def regions(end, population):
    # Intersecting with Q4 tiles proves that a Q8 face holds at most 128
    # selected vertices and each Q7 face at most 64.
    if population > 128:
        for axis in range(9):
            if end & (1 << axis) == 0:
                yield (1 << axis, 1 << axis)
    if population > 192:
        differing = [1 << axis for axis in range(9) if end & (1 << axis)]
        for a, b in combinations(differing[:4], 2):
            # Both endpoints are retained when either middle Q7 face is removed.
            yield (a | b, a)
            yield (a | b, b)


def add_endpoint_separation(formula, pool, physical, end, population):
    choices = list(regions(end, population))
    for mask, omitted in choices:
        sides = {v: pool.id() for v in range(512) if v & mask != omitted}
        assert 0 in sides and end in sides
        formula.extend([[-sides[0]], [sides[end]]])
        for u, v, edge in physical:
            if u in sides and v in sides:
                a, b = sides[u], sides[v]
                formula.extend([[-edge, -a, b], [-edge, a, -b]])
    return len(choices)
