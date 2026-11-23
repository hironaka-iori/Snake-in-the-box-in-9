"""Check a positive-only forbidden vertex pattern for an induced path in Q9."""
import gzip
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def parity(vertex):
    return vertex.bit_count() % 2


def terminal_counts(required):
    """Components of possible two-step transitions, counting forced terminals only."""
    side = parity(next(iter(required)))
    graph = {v: set() for v in range(512) if parity(v) == side}
    assert required <= graph.keys()
    for middle in range(512):
        if parity(middle) == side:
            continue
        neighbors = [middle ^ (1 << d) for d in range(9)]
        forced = required.intersection(neighbors)
        for left, right in combinations(neighbors, 2):
            if forced.issubset((left, right)):
                graph[left].add(right)
                graph[right].add(left)
    unseen = set(graph)
    counts = []
    while unseen:
        start = unseen.pop()
        stack = [start]
        count = 0
        while stack:
            v = stack.pop()
            count += v in required
            new = unseen.intersection(graph[v])
            unseen.difference_update(new)
            stack.extend(new)
        if count:
            counts.append(count)
    return sorted(counts)


def tiled(even, odd):
    return {32*y+x for y in range(16) for x in (odd if parity(y) else even)}


if __name__ == "__main__":
    occupied = tiled({0,1,3,4,7,13,15,20,22,24,25,26,29,30},
                     {2,6,8,9,11,12,14,16,17,18,21,23,27,31}) - {0,1}
    mandatory = tiled({4,13,22,25,26}, {6,9,12,17,18,23,27})
    assert mandatory <= occupied and len(mandatory) == 96
    for points, expected in [(mandatory,[40,56]), ({v for v in occupied if parity(v)},[55,56])]:
        counts = terminal_counts(points)
        assert counts == expected
        print(len(points), "required vertices; component terminal counts", counts)
    controls = 0
    with gzip.open(ROOT / "q9_port_followup_public191.txt.gz", "rt") as source:
        for line in source:
            path = list(map(int,line.split()))
            assert len(path) == len(set(path)) == 192
            assert all(((v ^ w).bit_count() == 1) == (i == j + 1)
                       for i,v in enumerate(path) for j,w in enumerate(path[:i]))
            for side in (0,1):
                assert terminal_counts(set(path[side::2])) == [96]
            controls += 1
    print(controls, "191-edge control paths, passed on both sides")
