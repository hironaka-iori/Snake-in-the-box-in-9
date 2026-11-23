"""Necessary footprint constraints after contracting one cube direction."""

from itertools import combinations

from q9_square_census import add_popcount


def add_column_cuts(formula, pool, selected_counts, endpoint, length, axes):
    dim = len(selected_counts)
    n = 1 << dim
    for axis in axes:
        mask = 1 << axis
        columns = [u for u in range(n) if not u & mask]
        presence = {}
        bipartition = [[], []]
        for u in columns:
            a, b = u + 1, (u ^ mask) + 1
            occupied = pool.id()
            formula.extend([[-a, occupied], [-b, occupied], [-occupied, a, b]])
            presence[u] = occupied
            bipartition[u.bit_count() % 2].append(occupied)
        for u in columns:
            a, b = u + 1, (u ^ mask) + 1
            adjacent = []
            for j in range(dim):
                if j == axis:
                    continue
                v = u ^ (1 << j)
                adjacent.append(presence[v])
                if u < v:
                    formula.append([-a, -b, -v - 1, -(v ^ mask) - 1])
            ports = 2 - int(u == 0) - int(u == (endpoint & ~mask))
            for extra in combinations(adjacent, ports+1):
                formula.append([-a, -b, *(-v for v in extra)])
            if ports:
                for omitted in combinations(adjacent, ports-1):
                    formula.append([-a, -b, *(v for v in adjacent if v not in omitted)])
        # A double column is one edge in the deleted direction. The projected
        # path starts at even parity and has length L minus the double count.
        endpoint_odd = bool(endpoint & mask)
        # Twice the even (odd) footprint count plus D is L+1 when the
        # footprint has even size, and L+2 (L) when it has odd size.
        odd_footprint = (length+1-endpoint_odd) % 2
        for colour, occupied in enumerate(bipartition):
            doubles = selected_counts[axis]
            bank = [[bit] for bit in doubles]
            bank[1].extend(occupied)
            combined = add_popcount(formula, pool, bank)
            target = length+1 + (1-2*colour)*odd_footprint
            assert 0 <= target < 1 << len(combined)
            for i, bit in enumerate(combined):
                assert bit is not None
                formula.append([bit if target >> i & 1 else -bit])
