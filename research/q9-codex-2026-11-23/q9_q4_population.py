"""Population limits over every four-dimensional subcube."""

from itertools import combinations

from q9_direction_frequency import append_upper_bound
from q9_square_census import add_popcount


def q4_populations(dim):
    for axes in combinations(range(dim),4):
        free = sum(1<<axis for axis in axes)
        rows = {}
        for v in range(1<<dim):
            rows.setdefault(v&~free,[]).append(v+1)
        yield from rows.values()


def add_q4_population(formula, pool, dim):
    for vertices in q4_populations(dim):
        count = add_popcount(formula,pool,[vertices[:]])
        append_upper_bound(formula,count,8)
