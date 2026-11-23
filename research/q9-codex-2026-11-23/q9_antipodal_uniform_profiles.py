"""Exhaust the antipodal case with minimum direction frequency 23."""

import json

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_221_global_interface_cuts import addition
from q9_direction_frequency import profile
from q9_endpoint_distance_bound import read_path
from q9_overlapping_cross18 import value_literals
from q9_tight_interface_search import certify


def partitions(total, minimum=1):
    if total == 0:
        yield ()
        return
    for first in range(minimum, total+1):
        for rest in partitions(total-first, first):
            yield (first, *rest)


def uniform_profiles():
    # Each of the nine counts is odd. Starting at 23 in each coordinate
    # leaves 14 transitions, i.e. seven units of two to distribute.
    return sorted(
        (23,)*(9-len(parts)) + tuple(23+2*n for n in parts)
        for parts in partitions(7)
    )


def solve_uniform(formula, endpoint, counts, header, stem, checker):
    assert header["distance"] == 9
    rows = uniform_profiles()
    assert len(rows) == len(set(rows)) == 15
    assert all(len(r)==9 and r[0]==23 and sum(r)==221 for r in rows)
    pool = IDPool(start_from=formula.nv+1)
    total = addition(formula, pool, *counts)
    formula.extend([[value] for value in value_literals(total,221)])
    selectors = []
    for row in rows:
        selector = pool.id()
        selectors.append(selector)
        literals = [lit for bits,n in zip(counts,row) for lit in value_literals(bits,n)]
        formula.extend([[-selector,lit] for lit in literals])
        formula.append([selector,*(-lit for lit in literals)])
    formula.append(selectors)
    order = sorted(range(len(rows)), key=lambda i:(len(set(rows[i])),rows[i]))
    print(json.dumps(dict(status="PROFILE_COVER_STARTED",minimum=23,profiles=rows,
                          budget_per_profile=header["budget"],clauses=len(formula.clauses))),flush=True)
    accepted = []
    tested = 0
    with Cadical195(bootstrap_with=formula) as solver:
        for i in order:
            row = rows[i]
            print(json.dumps(dict(status="PROFILE_STARTED",index=i,counts=row)),flush=True)
            before = solver.accum_stats()["conflicts"]
            solver.conf_budget(header["budget"])
            answer = solver.solve_limited(assumptions=[selectors[i]])
            status = "UNKNOWN"
            target = stem.with_name(f"{stem.name}_profile{i:02d}")
            if answer is False:
                status = certify(formula,[selectors[i]],target,checker)
                if status == "UNSAT_DRAT_VERIFIED":
                    accepted.append(i)
            elif answer:
                path = read_path(solver.get_model(),9,221,endpoint)
                assert tuple(profile(path,9))==row
                target.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                status = "SAT_PATH_VERIFIED"
            tested += 1
            print(json.dumps(dict(status=status,index=i,counts=row,conflicts=solver.accum_stats()["conflicts"]-before)),flush=True)
            if answer:
                break
    remaining = sorted(set(range(len(rows)))-set(accepted))
    print(json.dumps(dict(status="PROFILE_COVER_INCOMPLETE" if remaining else "PROFILE_COVER_CLOSED",
                          tested=tested,verified=sorted(accepted),remaining=remaining)),flush=True)
