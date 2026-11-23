"""Exhaustive cubing on the least-used direction for antipodal endpoints."""

import json

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_221_global_interface_cuts import addition
from q9_endpoint_distance_bound import read_path
from q9_overlapping_cross18 import value_literals
from q9_tight_interface_search import certify


def solve_cubes(formula, endpoint, counts, header, stem, checker):
    # Translation and parity-block sorting make the smallest frequency
    # counts[0]. Antipodal endpoints force it to be odd, and the average
    # is 221/9. The existing individual floor is three.
    assert header["distance"] == 9
    pool = IDPool(start_from=formula.nv+1)
    total = addition(formula, pool, *counts)
    formula.extend([[lit] for lit in value_literals(total,221)])
    frequencies = list(range(3,24,2))
    selectors = {}
    for value in frequencies:
        selector = pool.id()
        literals = value_literals(counts[0],value)
        formula.extend([[-selector,lit] for lit in literals])
        formula.append([selector,*(-lit for lit in literals)])
        selectors[value] = selector
    formula.append(list(selectors.values()))
    schedule = []
    for i, value in enumerate(frequencies[:(len(frequencies)+1)//2]):
        schedule.append(value)
        maximum = frequencies[-i-1]
        if maximum != value:
            schedule.append(maximum)
    assert sorted(schedule)==frequencies
    print(json.dumps(dict(status="COVER_STARTED",least_frequencies=frequencies,
                          clauses=len(formula.clauses),budget_per_cube=header["budget"])),flush=True)
    verified = []
    solved = []
    with Cadical195(bootstrap_with=formula) as solver:
        for value in schedule:
            selector = selectors[value]
            subproblem = stem.with_name(f"{stem.name}_min{value:02d}")
            print(json.dumps(dict(status="CUBE_STARTED",minimum=value)),flush=True)
            before = solver.accum_stats()["conflicts"]
            solver.conf_budget(header["budget"])
            answer = solver.solve_limited(assumptions=[selector])
            status = "UNKNOWN"
            if answer is False:
                status = certify(formula,[selector],subproblem,checker)
            elif answer:
                path = read_path(solver.get_model(),9,221,endpoint)
                assert sum(u^v==1 for u,v in zip(path,path[1:]))==value
                subproblem.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                status = "SAT_PATH_VERIFIED"
            if status == "UNSAT_DRAT_VERIFIED":
                verified.append(value)
            solved.append(value)
            print(json.dumps(dict(status=status,minimum=value,
                                  conflicts=solver.accum_stats()["conflicts"]-before)),flush=True)
            if status == "SAT_PATH_VERIFIED":
                break
    remaining = sorted(set(frequencies)-set(verified))
    print(json.dumps(dict(status="COVER_CLOSED" if not remaining else "COVER_INCOMPLETE",
                          tested=len(solved),verified=sorted(verified),remaining=remaining)),flush=True)
