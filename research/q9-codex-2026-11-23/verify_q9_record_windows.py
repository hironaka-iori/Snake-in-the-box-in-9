"""How many previously unknown 191-edge classes does a 195- or 196-snake need?

Test every 5-step initial transition word for the only coordinate-cycle type
that can avoid the elementary orbit-size obstruction at offset five.
"""
from collections import Counter
from itertools import product
from math import lcm


def partitions(total, maximum):
    if total == 0:
        yield ()
    for n in range(min(total, maximum), 0, -1):
        for suffix in partitions(total - n, n):
            yield (n,) + suffix


def induced_prefix(block, permutation):
    occupied = {0}
    endpoint = 0
    while True:
        for axis in block:
            v = endpoint ^ (1 << axis)
            neighbors = sum((v ^ (1 << a)) in occupied for a in range(9))
            if v in occupied or neighbors != 1:
                return len(occupied) - 1
            occupied.add(v)
            endpoint = v
        block = tuple(permutation[a] for a in block)


if __name__ == '__main__':
    types = list(partitions(9, 9))
    assert max(lcm(*t) for t in types) == 20
    assert [t for t in types if lcm(*t) >= 20] == [(5, 4)]
    pi = (1, 2, 3, 4, 0, 6, 7, 8, 5)
    distribution = Counter(induced_prefix(word, pi) for word in product(range(9), repeat=5))
    assert sum(distribution.values()) == 59049 and max(distribution) == 44
    print('cycle types', len(types), '5-step words',sum(distribution.values()),'maximum induced prefix',max(distribution))
