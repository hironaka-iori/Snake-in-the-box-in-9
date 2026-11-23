"""Necessary two-coordinate balance for an induced even-length path in Q9."""
from functools import lru_cache
from itertools import combinations
import gzip
from pathlib import Path


@lru_cache(None)
def bipartite_edges(dim, a, b):
    """Upper bound on edges between a vertices of one parity and b of the other."""
    if a > b:
        return bipartite_edges(dim, b, a)
    if not a:
        return 0
    if dim == 1:
        return 1
    half = 2 ** (dim - 2)
    # Split into two (dim-1)-cubes. Crossing edges form a matching in each parity.
    return max(
        bipartite_edges(dim-1, i, j) + bipartite_edges(dim-1, a-i, b-j)
        + min(i, b-j) + min(j, a-i)
        for i in range(max(0, a-half), min(a, half)+1)
        for j in range(max(0, b-half), min(b, half)+1)
    )


@lru_cache(None)
def host_cap(holes):
    # Any k same-sheet intermediates each see at least five holes in Q7.
    for k in range(1, 65):
        if bipartite_edges(7, holes, k) < 5*k:
            return k-1
    return 64


def contracted_edge_bound(m, t):
    holes = 128-m+t
    return max(
        64-max(h, holes-h) + host_cap(h) + host_cap(holes-h) + 2*t
        for h in range(max(0, holes-64), min(holes, 64)+1)
    )


def minimum_minority(m):
    return next(t for t in range(m//2+1) if contracted_edge_bound(m,t) >= m-1)


def check_recurrence():
    # Exhaustive cross-check on ordered parity-set cardinalities through Q4.
    for dim in range(1, 5):
        n = 1 << dim
        left = [v for v in range(n) if v.bit_count()%2 == 0]
        right = [v for v in range(n) if v.bit_count()%2]
        neighborhoods = [sum(1 << i for i,v in enumerate(right) if (v^u).bit_count()==1) for u in left]
        for chosen in range(1 << len(left)):
            counts = [0]*len(right)
            for i,nb in enumerate(neighborhoods):
                if chosen >> i & 1:
                    for j in range(len(right)):
                        counts[j] += nb >> j & 1
            total = 0
            for b,val in enumerate(sorted(counts, reverse=True), 1):
                total += val
                assert total <= bipartite_edges(dim, chosen.bit_count(), b)


def check_path_bank():
    bank = Path(__file__).with_name("q9_port_followup_public191.txt.gz")
    count = 0
    minimum = 96
    with gzip.open(bank, "rt") as f:
        for line in f:
            path = list(map(int, line.split()))
            assert len(path)==192 and len(set(path))==192 and all(0<=x<512 for x in path)
            for i,v in enumerate(path):
                for j in range(i):
                    assert ((v^path[j]).bit_count()==1) == (j==i-1)
            for sub in (path[:-1], path[1:]):
                even_times = sub[::2]
                for i,j in combinations(range(9),2):
                    same = sum(((u>>i)^(u>>j))&1 for u in even_times)
                    t = min(same, len(even_times)-same)
                    assert contracted_edge_bound(len(even_times),t) >= len(even_times)-1
                    minimum = min(minimum,t)
                    count += 1
    print("190-edge control cases:", count, "minimum observed minority:", minimum)


if __name__ == "__main__":
    check_recurrence()
    for m in (96,97,101,106,111,115,116):
        print("edges",2*m-2,"minority required",minimum_minority(m))
    print("bounds at 230 edges for t=0..20:",[contracted_edge_bound(116,t) for t in range(21)])
    check_path_bank()
