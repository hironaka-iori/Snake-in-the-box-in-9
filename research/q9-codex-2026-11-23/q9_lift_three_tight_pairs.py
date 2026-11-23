"""Test whether three nine-use directions lift from Q6 profiles into a Q9 path."""
import argparse
import json
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_direction_frequency import build
from q9_endpoint_distance_bound import read_path
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from q9_three_axis_profiles import formula
from q9_three_tight_pairs import BONDS
from q9_tight_interface_search import certify


ROOT = Path(__file__).resolve().parent/'q9_endpoint_distance_checks'


def surviving_profiles():
    def load(name):
        return json.loads((ROOT/name).read_text())
    saved = load('q9_three_tight_pairs.json')['representatives']
    f,edges,components,cross = formula(
        (9,9,9),7,
        load('verified_exact_interface_cuts_full.json'),
        load('verified_q6_star_cuts_first13.json'),
    )
    groups = (edges,components,[cross[b] for b in BONDS])
    with Cadical195(bootstrap_with=f) as solver:
        for row in saved:
            fixed = [bit if i<n else -bit
                     for bank,vals in zip(groups,row)
                     for bits,n in zip(bank,vals)
                     for i,bit in enumerate(bits)]
            if solver.solve(assumptions=fixed):
                yield row


def add_projected_rows(f, rows, axes=(0,1,2)):
    """Require the physical face counts to match one independently covered row."""
    pool = IDPool(start_from=f.nv+1)
    labels = [sum((u>>a&1)<<i for i,a in enumerate(axes)) for u in range(512)]
    vertices = [[] for _ in range(8)]
    edges = [[] for _ in range(8)]
    crossings = {b:[] for b in BONDS}
    for u in range(512):
        layer = labels[u]
        vertices[layer].append(u+1)
        for a in range(9):
            v = u|(1<<a)
            if u==v:
                continue
            bond = pool.id()
            f.extend([[-bond,u+1],[-bond,v+1],[bond,-u-1,-v-1]])
            bank = edges[layer] if a not in axes else crossings[layer,labels[v]]
            bank.append(bond)
    groups = tuple([add_popcount(f,pool,[bank]) for bank in banks]
                   for banks in (edges,vertices,crossings.values()))
    choices = []
    for e,c,r in rows:
        candidate = pool.id()
        choices.append(candidate)
        for counters,values in zip(groups,(e,[a+b for a,b in zip(e,c)],r)):
            for bits,n in zip(counters,values):
                f.extend([[-candidate,bit] for bit in value_literals(bits,n)])
    f.append(choices)

def search(distance, budget, checker, stem, rows=None, axes=(0,1,2), usage=(9,9,9)):
    rows = list(surviving_profiles()) if rows is None else rows
    f,end,counts = build(9,221,distance)
    f.extend([[bit] for a,n in zip(axes,usage) for bit in value_literals(counts[a],n)])
    add_projected_rows(f, rows, axes)
    header = dict(distance=distance, profiles=len(rows), budget=budget,clauses=len(f.clauses), usage=usage)
    print(json.dumps(dict(status='STARTED',**header)),flush=True)
    with Cadical195(bootstrap_with=f) as solver:
        solver.conf_budget(budget)
        result = solver.solve_limited()
        status = 'UNKNOWN'
        if result is False:
            # The helper expects a nonempty set of assumptions.
            status = certify(f,[end+1],stem,checker)
        elif result:
            path = read_path(solver.get_model(),9,221,end)
            stem.with_suffix('.path').write_text(' '.join(map(str,path))+'\n')
            status = 'SAT_PATH_VERIFIED'
        print(json.dumps(dict(status=status,conflicts=solver.accum_stats()['conflicts'],
                              **header)),flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('distance',type=int,choices=(3,5,7,9))
    p.add_argument('budget',type=int)
    p.add_argument('stem',type=Path)
    p.add_argument('checker')
    p.add_argument('--catalogue',type=Path)
    p.add_argument('--verified-selection',type=Path)
    args = p.parse_args()
    if args.catalogue:
        assert args.distance<9 and args.verified_selection
        records = [json.loads(line) for line in args.verified_selection.read_text().splitlines()]
        assert records[-1]['status']=='VERIFIED'
        bank = json.loads(args.catalogue.read_text())['representatives']
        rows = [bank[i] for i in records[-1]['indices']]
        search(args.distance,args.budget,args.checker,args.stem,
               rows,(0,1,args.distance),(9,9,10))
    else:
        search(args.distance,args.budget,args.checker,args.stem)

