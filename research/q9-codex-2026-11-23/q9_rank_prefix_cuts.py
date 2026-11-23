"""Expose induced-path prefixes and their unique physical crossing edge."""

from pysat.card import CardEnc, EncType

from q9_anchor_distances import exclude_interval
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount


def add_prefix_cuts(formula, pool, phase, length, steps):
    n = len(phase)
    for step in steps:
        if not 0 <= step < length:
            raise ValueError("Each cut must be between consecutive path positions")
        before = [pool.id() for _ in phase]
        after = [pool.id() for _ in phase]
        colours = [[], []]
        for vertex, bits in enumerate(phase):
            present = vertex + 1
            left, right = before[vertex], after[vertex]
            formula.extend([[-left, present], [-right, present],
                            [-present, left, right], [-left, -right]])
            weight = vertex.bit_count()
            cutoff = (step - weight) // 2
            exclude_interval(formula, left, bits, cutoff + 1, (1 << len(bits)) - 1)
            exclude_interval(formula, right, bits, 0, cutoff)
            colours[weight % 2].append(left)
        for colour, vertices in enumerate(colours):
            bits = add_popcount(formula, pool, [vertices])
            for lit in value_literals(bits, (step + 2 - colour) // 2):
                formula.append([lit])

        crossings = []
        for vertex in range(n):
            for axis in range(n.bit_length() - 1):
                neighbor = vertex ^ (1 << axis)
                crossing = pool.id()
                left, right = before[vertex], after[neighbor]
                formula.extend([[-crossing, left], [-crossing, right],
                                [-left, -right, crossing]])
                crossings.append(crossing)
        formula.extend(CardEnc.equals(crossings, 1, vpool=pool,
                                      encoding=EncType.seqcounter).clauses)
