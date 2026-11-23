"""Solve the degree relaxation, separating any induced cycles it finds."""

import json

from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_tight_interface_search import certify
from verify_q9_free_dimension_cuts import parts, deg


def cycle_components(points, dim, endpoints):
    components = parts(points,dim)
    route = [part for part in components if endpoints[0] in part]
    assert len(route)==1 and endpoints[1] in route[0]
    cycles = []
    for part in components:
        if part is route[0]:
            continue
        assert not set(endpoints)&part
        assert all(deg(part,u,dim)==2 for u in part)
        cycles.append(sorted(part))
    return cycles


def solve_relaxation(formula, endpoint, header, stem, checker):
    status = "UNKNOWN"
    cycles = []
    with Cadical195(bootstrap_with=formula) as solver:
        while (remaining:=header["budget"]-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(remaining)
            answer = solver.solve_limited()
            if answer is False:
                status = certify(formula,[endpoint+1],stem,checker)
                break
            if answer is None:
                break
            model = solver.get_model()
            points = {x-1 for x in model if 1<=x<=512}
            assert len(points)==222
            detached = cycle_components(points,9,(0,endpoint))
            if not detached:
                route = read_path(model,9,221,endpoint)
                stem.with_suffix(".path").write_text(" ".join(map(str,route))+"\n")
                status = "SAT_PATH_VERIFIED"
                break
            for cycle in detached:
                assert cycle not in cycles
                clause = [-u-1 for u in cycle]
                formula.append(clause)
                solver.add_clause(clause)
                cycles.append(cycle)
            print(json.dumps(dict(status="CYCLE_CUTS",lengths=list(map(len,detached)),
                                  cuts=len(cycles),conflicts=solver.accum_stats()["conflicts"])),flush=True)
        conflicts = solver.accum_stats()["conflicts"]
    if cycles:
        stem.with_suffix(".cycles.json").write_text(json.dumps(cycles)+"\n")
    print(json.dumps(dict(status=status,conflicts=conflicts,cycle_cuts=len(cycles),**header)),flush=True)
