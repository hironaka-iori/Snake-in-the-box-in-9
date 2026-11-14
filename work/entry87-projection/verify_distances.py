"""Rebuild admissible run distances directly from all indexed pairs of vertices."""
from functools import cache
from itertools import combinations


@cache
def cube_composition(first, second):
    """Place the first point at zero and the middle point at a canonical word."""
    possible = set()
    for left in first:
        middle = (1 << left) - 1
        for last in range(64):
            if (middle ^ last).bit_count() in second:
                possible.add(last.bit_count())
    return frozenset(possible)


def check_table(path, free, proposed, families):
    fixed_mask = 511 ^ sum(1 << bit for bit in free)
    assert len(free) == 6
    base = [v & fixed_mask for v in path]
    run = [0]
    for a, b in zip(base, base[1:]):
        run.append(run[-1] + int(a == b))
    n = run[-1] + 1
    assert n == len(proposed)
    allowed = [[frozenset(range(abs(i-j) % 2, min(abs(i-j), 6)+1, 2))
                for j in range(n)] for i in range(n)]
    for i, j in combinations(range(len(path)), 2):
        a, b = run[i], run[j]
        fixed_distance = (base[i] ^ base[j]).bit_count()
        allowed[a][b] = frozenset(h for h in allowed[a][b]
                                  if (h + fixed_distance == 1 if j == i+1
                                      else h + fixed_distance >= 2))
        allowed[b][a] = allowed[a][b]
    passes = 0
    while True:
        changed = False
        for a, b in combinations(range(n), 2):
            s = allowed[a][b]
            for k in range(n):
                if k != a and k != b:
                    s = s & cube_composition(allowed[a][k], allowed[k][b])
            if s != allowed[a][b]:
                allowed[a][b] = allowed[b][a] = s
                changed = True
        passes += 1
        if not changed:
            break
    for a in range(n):
        for b in range(n):
            assert proposed[a][b] == sum(1 << h for h in allowed[a][b]), (a,b)
    for family in families:
        assert len(set(family)) == len(family)
        assert len({r % 2 for r in family}) == 1
        assert all(0 not in allowed[a][b] for a,b in combinations(family,2))
    return passes
