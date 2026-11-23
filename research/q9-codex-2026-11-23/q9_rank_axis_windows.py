"""Every long induced subpath must vary enough cube coordinates."""

from pysat.card import CardEnc, EncType

from q9_anchor_distances import exclude_interval


def add_axis_windows(formula, pool, phase, windows):
    n = len(phase)
    dimension = n.bit_length() - 1
    for start, stop, minimum_axes in windows:
        in_window = []
        for vertex, bits in enumerate(phase):
            weight = vertex.bit_count()
            low = (start - weight + 1) // 2
            high = (stop - weight) // 2
            maximum = (1 << len(bits)) - 1
            outside, inside = pool.id(), pool.id()
            formula.extend([[-inside, vertex+1], [-outside, vertex+1],
                            [-vertex-1, inside, outside], [-inside, -outside]])
            exclude_interval(formula, inside, bits, 0, low-1)
            exclude_interval(formula, inside, bits, high+1, maximum)
            exclude_interval(formula, outside, bits, low, high)
            in_window.append(inside)
        varied = []
        for axis in range(dimension):
            values = [[], []]
            for vertex, inside in enumerate(in_window):
                values[(vertex >> axis) & 1].append(inside)
            active = pool.id()
            varied.append(active)
            for literals in values:
                formula.append([-active, *literals])
        formula.extend(CardEnc.atleast(varied, minimum_axes, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
