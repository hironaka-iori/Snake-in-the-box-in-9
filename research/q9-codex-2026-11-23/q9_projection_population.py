"""Derive and encode minimum face populations at low pair crossing counts."""
from collections import defaultdict
from functools import lru_cache
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

from verify_q9_free_dimension_cuts import edge7


@lru_cache(maxsize=None)
def populations(limit):
    """Walk on the four faces, starting at 00, and bound each face's size."""
    states = {(0, (1, 0, 0, 0))}
    minima = {}
    for k in range(limit + 1):
        rows = []
        for _, components in states:
            caps = [edge7(c) for c in components]
            shortfall = sum(caps) + k - 221
            if shortfall >= 0:
                rows.append([c + max(0, cap - shortfall)
                             for c, cap in zip(components, caps)])
        if k >= 17 and rows:
            minima[k] = tuple(map(min, zip(*rows)))
        states = {(end ^ move, tuple(count + (i == end ^ move)
                                    for i, count in enumerate(components)))
                  for end, components in states for move in (1, 2)}
    return minima


@lru_cache(maxsize=None)
def interface_ranges():
    from q9_projection_interfaces import summarize
    return summarize(21)


def add_population_cut(f, i, j, interfaces=False):
    """For one pair, force all faces to have at least 54 points if k <= 21."""
    bounds = populations(21)
    assert all(bounds[k] == (54,) * 4 for k in range(17,22))
    if interfaces:
        rows = interface_ranges()
        assert all(all(54 <= lower <= upper <= 56 for lower, upper in row["point_ranges"])
                   for row in rows)
    pool = IDPool(start_from=f.nv + 1)
    cross = []
    for axis in (i,j):
        for v in range(512):
            if v >> axis & 1:
                continue
            w = v ^ (1 << axis)
            edge = pool.id()
            f.extend([[-edge,v+1],[-edge,w+1],[edge,-v-1,-w-1]])
            cross.append(edge)
    # If low is false, crossings must number at least 22.
    low = pool.id()
    gate = CardEnc.atleast(cross,22,vpool=pool,encoding=EncType.cardnetwrk)
    f.extend([[low,*clause] for clause in gate.clauses])
    faces = defaultdict(list)
    for v in range(512):
        faces[(v >> i & 1) + 2*(v >> j & 1)].append(v+1)
    for points in faces.values():
        gate = CardEnc.atleast(points,54,vpool=pool,encoding=EncType.cardnetwrk)
        f.extend([[-low,*clause] for clause in gate.clauses])
        if interfaces:
            upper = CardEnc.atmost(points,56,vpool=pool,encoding=EncType.cardnetwrk)
            f.extend([[-low,*clause] for clause in upper.clauses])


if __name__ == "__main__":
    print(populations(24))
