"""Check Q6 forest edge counts with a prescribed split between the two colours."""
import argparse
import json
import subprocess
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q9_short_cycle_clauses import add_small_cycles
from verify_q9_free_dimension_cuts import deg, parts


def build(e,b,w):
    f = CNF()
    pool = IDPool(start_from=65)
    bond = []
    for u in range(64):
        adj = [u^(1<<axis) for axis in range(6)]
        for tri in combinations(adj,3):
            f.append([-u-1,*(-x-1 for x in tri)])
        for v in adj:
            if u<v:
                x = pool.id()
                bond.append(x)
                f.extend([[-x,u+1],[-x,v+1],[x,-u-1,-v-1]])
    def fixed(inputs,n):
        f.extend(CardEnc.equals(inputs,n,vpool=pool,encoding=EncType.cardnetwrk))
    fixed(bond,e)
    fixed([u+1 for u in range(64) if u.bit_count()%2==0],b)
    fixed([u+1 for u in range(64) if u.bit_count()%2==1],w)
    add_small_cycles(f,6,3)
    return f


def trial(e,b,w,budget,checker,out):
    f = build(e,b,w)
    cycles = []
    with Cadical195(bootstrap_with=f) as solver:
        while (left:=budget-solver.accum_stats()['conflicts'])>0:
            solver.conf_budget(left)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                name = out/f'forest_{e}_{b}_{w}'
                with Cadical195(bootstrap_with=f,with_proof=True) as certifier:
                    assert certifier.solve() is False
                    name.with_suffix('.drat').write_text('\n'.join(certifier.get_proof())+'\n')
                f.to_file(str(name.with_suffix('.cnf')))
                checked = subprocess.run([checker,str(name.with_suffix('.cnf')),str(name.with_suffix('.drat'))],
                                         capture_output=True,check=True)
                assert b's VERIFIED' in checked.stdout
                return dict(status='UNSAT_DRAT_VERIFIED',cycles=cycles,proof=str(name.with_suffix('.drat')))
            points = {u-1 for u in solver.get_model() if 1<=u<=64}
            assert len(points)==b+w and sum(u.bit_count()%2==0 for u in points)==b
            degree = {u:deg(points,u,6) for u in points}
            assert max(degree.values())<=2 and sum(degree.values())==2*e
            found = [sorted(s) for s in parts(points,6) if all(degree[u]==2 for u in s)]
            if not found:
                assert len(parts(points,6))==b+w-e
                return dict(status='SAT_WITNESS_VERIFIED',points=sorted(points))
            for cycle in found:
                cut = [-u-1 for u in cycle]
                solver.add_clause(cut)
                f.append(cut)
                cycles.append(cycle)
        return dict(status='UNKNOWN',cycles=cycles,conflicts=solver.accum_stats()['conflicts'])


if __name__=='__main__':
    p = argparse.ArgumentParser()
    p.add_argument('checker')
    p.add_argument('out',type=Path)
    p.add_argument('--budget',type=int,default=30000)
    args = p.parse_args()
    for e in (24,23,22):
        for b in range((e+1)//2,17):
            for w in range(max(b,e+1-b),33-b):
                print(json.dumps(dict(status='STARTED',edges=e,colors=[b,w])),flush=True)
                result = trial(e,b,w,args.budget,args.checker,args.out)
                print(json.dumps(dict(edges=e,colors=[b,w],**result)),flush=True)

