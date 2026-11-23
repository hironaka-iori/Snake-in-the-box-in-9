"""Partition a complete 221-edge endpoint model by unit-propagation lookahead."""

import argparse
import json
from pathlib import Path

from pysat.solvers import Cadical195

from q9_221_compact_selector import build_compact
from q9_endpoint_distance_bound import read_path
from q9_lazy_colour_cycles import cycle_components
from q9_tight_interface_search import certify


def cover(solver,variables,assumptions,depth):
    consistent, propagated = solver.propagate(assumptions=list(assumptions))
    assigned = {abs(x) for x in propagated}|{abs(x) for x in assumptions}
    remaining = [v for v in variables if v not in assigned]
    if depth==0 or not consistent or not remaining:
        return dict(assumptions=list(assumptions),unit_conflict=not consistent)
    score = None
    split = None
    for var in remaining:
        sizes = []
        auxiliary = []
        failed = 0
        for lit in (-var,var):
            ok,forced = solver.propagate(assumptions=[*assumptions,lit])
            failed+=not ok
            auxiliary.append(len(forced))
            sizes.append(sum(abs(x) in variables and abs(x) not in assigned for x in forced))
            if not ok:
                sizes[-1] += len(variables)
        # Avoid spending a split on a literal already forced in this node.
        if failed==1:
            continue
        candidate = failed, min(sizes), sizes[0]*sizes[1], min(auxiliary), -var
        if score is None or candidate>score:
            score,split=candidate,var
        if failed==2:
            break
    if split is None:
        return dict(assumptions=list(assumptions),unit_conflict=False)
    return dict(split=split,
                negative=cover(solver,variables,(*assumptions,-split),depth-1),
                positive=cover(solver,variables,(*assumptions,split),depth-1))


def leaves(tree,expected=()):
    if "split" not in tree:
        assert tuple(tree["assumptions"])==expected
        yield tree
        return
    pivot=tree["split"]
    assert pivot>0 and all(pivot!=abs(lit) for lit in expected)
    yield from leaves(tree["negative"],(*expected,-pivot))
    yield from leaves(tree["positive"],(*expected,pivot))


def run(d,budget,depth,checker,stem,ledger):
    formula,end=build_compact(221,d,json.loads(ledger.read_text()))
    with Cadical195(bootstrap_with=formula) as solver:
        pivots = {v+1 for v in range(512)
                  if min(v.bit_count(),(v^end).bit_count())>1}
        tree=cover(solver,pivots,(),depth)
        cubes=list(leaves(tree))
        stem.with_suffix(".tree.json").write_text(json.dumps(tree)+"\n")
        print(json.dumps(dict(status="LOOKAHEAD_COVER_STARTED",distance=d,leaves=len(cubes),
                              unit_conflicts=sum(c["unit_conflict"] for c in cubes),
                              clauses=len(formula.clauses),budget_per_leaf=budget)),flush=True)
        verified=[]
        cycles=set()
        for i in sorted(range(len(cubes)),key=lambda j:not cubes[j]["unit_conflict"]):
            assumptions=cubes[i]["assumptions"]
            output=stem.with_name(f"{stem.name}_leaf{i:03d}")
            print(json.dumps(dict(status="LEAF_STARTED",index=i,assumptions=assumptions)),flush=True)
            prior=solver.accum_stats()["conflicts"]
            status="UNKNOWN"
            while (left:=budget-(solver.accum_stats()["conflicts"]-prior))>0:
                solver.conf_budget(left)
                answer=solver.solve_limited(assumptions=assumptions)
                if answer is None:
                    break
                if answer is False:
                    status=certify(formula,assumptions or [end+1],output,checker)
                    if status=="UNSAT_DRAT_VERIFIED":
                        verified.append(i)
                    break
                model=solver.get_model()
                selected={u-1 for u in model if 1<=u<=512}
                detached=cycle_components(selected,9,(0,end))
                if not detached:
                    path=read_path(model,9,221,end)
                    output.with_suffix(".path").write_text(" ".join(map(str,path))+"\n")
                    status="SAT_PATH_VERIFIED"
                    break
                for loop in detached:
                    key=tuple(loop)
                    assert key not in cycles
                    cycles.add(key)
                    clause=[-u-1 for u in loop]
                    formula.append(clause)
                    solver.add_clause(clause)
            print(json.dumps(dict(status=status,index=i,cycle_cuts=len(cycles),
                                  conflicts=solver.accum_stats()["conflicts"]-prior)),flush=True)
            if status=="SAT_PATH_VERIFIED":
                break
    if cycles:
        stem.with_suffix(".cycles.json").write_text(json.dumps(sorted(cycles))+"\n")
    remaining=sorted(set(range(len(cubes)))-set(verified))
    print(json.dumps(dict(status="LOOKAHEAD_COVER_INCOMPLETE" if remaining else "LOOKAHEAD_COVER_CLOSED",
                          distance=d,verified=verified,remaining=remaining)),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("distance",type=int,choices=(3,5,7,9))
    parser.add_argument("budget",type=int)
    parser.add_argument("depth",type=int,choices=range(1,8))
    parser.add_argument("checker")
    parser.add_argument("stem",type=Path)
    parser.add_argument("ledger",type=Path)
    a=parser.parse_args()
    run(a.distance,a.budget,a.depth,a.checker,a.stem,a.ledger)
