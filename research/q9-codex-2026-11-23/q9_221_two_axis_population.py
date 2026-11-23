"""Q2 projection bounds on Q8 half populations and local crossings."""

from pysat.formula import IDPool

from q9_direction_frequency import append_order, append_upper_bound
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from verify_q9_free_dimension_cuts import edge7


def projection_states(first, second):
    # Retain endpoint, numbers of flips in the first axis, second-axis flips
    # in its zero half, and visit counts of the four Q7 slices.
    states = {(0, 0, 0, (1, 0, 0, 0))}
    for step in range(first + second):
        following = set()
        for layer, used_first, zero_crossings, visits in states:
            if used_first < first:
                nxt = layer ^ 1
                updated = list(visits)
                updated[nxt] += 1
                following.add((nxt, used_first + 1, zero_crossings, tuple(updated)))
            if step - used_first < second:
                nxt = layer ^ 2
                updated = list(visits)
                updated[nxt] += 1
                following.add((nxt, used_first, zero_crossings + int(layer & 1 == 0),
                               tuple(updated)))
        states = following
    return {(zero_crossings, visits) for _, _, zero_crossings, visits in states}


def allowed_populations(length, first, second):
    rows = set()
    for zero_crossings, visits in projection_states(first, second):
        other_crossings = second - zero_crossings
        components = visits[0] + visits[2] - zero_crossings
        assert components == first // 2 + 1
        cap_zero = zero_crossings + edge7(visits[0]) + edge7(visits[2])
        cap_one = other_crossings + edge7(visits[1]) + edge7(visits[3])
        least = length - first - cap_one + components
        most = cap_zero + components
        rows.update((population, zero_crossings) for population in range(least, most + 1))
    return rows


def contact_populations(first, second):
    """Project the previously checked Q7 contact restrictions."""
    from q9_projection_interfaces import profiles

    return {
        (vertices[0] + vertices[2], crossings[2])
        for total, end, crossings, _, vertices in profiles(first + second)
        if total == first + second
        and end == first % 2 + 2 * (second % 2)
        and crossings[0] + crossings[1] == first
    }


def add_fixed_profiles(formula, physical, length, profile, contacts=False):
    assert length == 221
    pool = IDPool(start_from=formula.nv + 1)
    population = add_popcount(formula, pool, [[v + 1 for v in range(0, 512, 2)]])
    if contacts:
        # Complementing all nine bits swaps the endpoints and the two halves.
        append_upper_bound(formula, population, 111)
    local_counts = []
    for axis in (1, 2):
        if contacts:
            rows = contact_populations(profile[0], profile[axis])
        else:
            rows = allowed_populations(length, profile[0], profile[axis])
        marks = []
        inside = add_popcount(formula, pool, [[
            bond for u, v, bond in physical if u & 1 == 0 and u ^ v == 1 << axis
        ]])
        local_counts.append(inside)
        for n, crossings in sorted(rows):
            select = pool.id()
            marks.append(select)
            target = value_literals(population, n) + value_literals(inside, crossings)
            formula.extend([[-select, lit] for lit in target])
        formula.append(marks)
    if contacts and profile[1] == profile[2]:
        # Swap equal-frequency directions without changing the first half.
        append_order(formula, pool, *local_counts)
