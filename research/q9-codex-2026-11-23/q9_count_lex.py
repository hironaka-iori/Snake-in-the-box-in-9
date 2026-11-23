"""Symmetry breaking that preserves parity-block direction sorting."""

from pysat.formula import IDPool


def lex_leader(formula, pool, pairs, guard=()):
    active = list(guard)
    for i, (left, right) in enumerate(pairs):
        formula.append([*active, -left, right])
        if i+1 == len(pairs):
            break
        equal_prefix = pool.id()
        formula.extend([[*active, left, right, equal_prefix],
                        [*active, -left, -right, equal_prefix]])
        active = [-equal_prefix]


def equality(formula, pool, left, right):
    differences = []
    for a, b in zip(left, right):
        different = pool.id()
        formula.extend([[-a, -b, -different], [a, b, -different],
                        [a, -b, different], [-a, b, different]])
        differences.append(different)
    same = pool.id()
    formula.extend([[-same, -lit] for lit in differences])
    formula.append([same, *differences])
    return same


def add_count_lex(formula, counts, endpoint, distance):
    dim = len(counts)
    n = 1 << dim
    pool = IDPool(start_from=formula.nv+1)
    reversal = [(u+1, (u ^ endpoint)+1) for u in range(n)
                if u < (u ^ endpoint)]
    lex_leader(formula, pool, reversal)
    for a, b in zip(range(dim-1), range(1, dim)):
        if b == distance:
            continue
        mask = (1 << a) | (1 << b)
        pairs = [(u+1, (u ^ mask)+1) for u in range(n)
                 if u & mask == 1 << a]
        same = equality(formula, pool, counts[a], counts[b])
        lex_leader(formula, pool, pairs, [-same])
