"""Exhaustively enumerate placements of a dense Q6 neighbour around a 25-edge anchor."""
import argparse
import gzip
import json
from pathlib import Path

from pysat.solvers import Cadical195

from q6_star_interfaces import check, formula
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import deg, parts


def placements(mask,leaf,budget,checker):
    e,c,cross = leaf
    fixed = {u for u in range(64) if mask>>u&1}
    allowed = set(range(64))-{u for u in fixed if deg(fixed,u,6)==2}
    f = formula(mask,(leaf,))
    valid,cycles = [],[]
    with Cadical195(bootstrap_with=f) as solver:
        while (remaining:=budget-solver.accum_stats()['conflicts'])>0:
            solver.conf_budget(remaining)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                # Check completeness against the final CNF, including every
                # model blocker and cycle cut as an input clause.
                with Cadical195(bootstrap_with=f,with_proof=True) as replay:
                    assert replay.solve() is False
                    proof = '\n'.join(replay.get_proof() or ['0'])+'\n'
                check(f,proof,checker)
                return dict(status='CATALOGUE_COVERAGE_VERIFIED',models=valid,cycles=cycles,proof=proof)
            model = set(solver.get_model())
            selected = {v for v in allowed if v+1 in model}
            full = fixed|{v+64 for v in selected}
            assert len(selected)==e+c and len(selected&fixed)==cross
            assert sum(deg(selected,u,6) for u in selected)==2*e
            assert max(deg(full,u,7) for u in full)<=2
            rings = [sorted(s) for s in parts(full,7) if all(deg(s,u,7)==2 for u in s)]
            if rings:
                for ring in rings:
                    cut = [-(u-64)-1 for u in ring if u>=64]
                    assert cut
                    cycles.append(ring)
                    f.append(cut)
                    solver.add_clause(cut)
            else:
                bitmask = sum(1<<v for v in selected)
                valid.append(f'{bitmask:016x}')
                cut = [-u-1 for u in sorted(selected)]
                f.append(cut)
                solver.add_clause(cut)
    return dict(status='UNKNOWN',models=valid,cycles=cycles,conflicts=solver.accum_stats()['conflicts'])


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('checker')
    p.add_argument('archive',type=Path)
    p.add_argument('--budget',type=int,default=100000)
    p.add_argument('--case',type=int,nargs=4,action='append',metavar=('CENTER_COMPONENTS','EDGES','COMPONENTS','CROSSES'))
    p.add_argument('--anchor-edges',type=int,choices=(24,25,26),default=25)
    a = p.parse_args()
    with gzip.open(a.archive,'wt') as archive:
        cases = a.case or [(3,24,4,2),(3,24,3,2)]
        if a.anchor_edges==24:
            assert all(case[0]==4 for case in cases), 'The verified 24-edge anchor has four components'
        for center,e,c,r in cases:
            leaf = e,c,r
            for i,mask in enumerate(anchor_list(center,a.anchor_edges)):
                result = placements(mask,leaf,a.budget,a.checker)
                record = dict(leaf=leaf,center_components=center,center_edges=a.anchor_edges,anchor=f'{mask:016x}',**result)
                archive.write(json.dumps(record)+'\n')
                archive.flush()
                print(json.dumps(dict(index=i,leaf=leaf,anchor=record['anchor'],
                    status=record['status'],models=len(record['models']))),flush=True)

