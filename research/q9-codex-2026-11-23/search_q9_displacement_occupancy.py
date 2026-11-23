"""Distance-one tube, factored by occupancy of cube vertices."""
import json
import sys
from collections import defaultdict
from itertools import combinations
from pathlib import Path
from pysat.solvers import Cadical195
from search_q9_unit_displacements import valid

def solve(p, axes, budget):
    dom=[{v^(1<<a):1+len(axes)*i+k for k,a in enumerate(axes)} for i,v in enumerate(p)]
    at=defaultdict(list)
    occupied=lambda v:len(p)*len(axes)+v+1
    with Cadical195() as s:
        for i,row in enumerate(dom):
            s.add_clause(list(row.values()))
            for a,b in combinations(row.values(),2):s.add_clause([-a,-b])
            for v,a in row.items():at[v].append(a)
        for v,lits in at.items():
            occ=occupied(v)
            s.add_clause([-occ,*lits])
            for a in lits:s.add_clause([-a,occ])
            for a,b in combinations(lits,2):s.add_clause([-a,-b])
        for i,row in enumerate(dom):
            adjacent=[dom[j] for j in (i-1,i+1) if 0<=j<len(dom)]
            for v,a in row.items():
                nb=[v^(1<<d) for d in range(9)]
                for near in adjacent:s.add_clause([-a,*[near[w] for w in nb if w in near]])
                for w in nb:
                    if w in at:s.add_clause([-a,-occupied(w),*[near[w] for near in adjacent if w in near]])
        s.set_phases([row[next(iter(row))] for row in dom])
        s.conf_budget(budget)
        ans=s.solve_limited()
        if ans is not True:return ("UNSAT" if ans is False else "UNKNOWN"),None
        model=set(s.get_model())
        walk=[next(v for v,a in row.items() if a in model) for row in dom]
        assert valid(walk)
        return "FOUND",walk

if __name__=="__main__":
    bank=[list(map(int,r.split())) for r in Path("q9_onechord_expanded_800.txt").read_text().splitlines()]
    seed=[0]
    for d in Path("q9_reordered_segments_20261120/reference191.words").read_text().split()[0]:
        seed.append(seed[-1]^(1<<int(d)))
    for idx in [-1,*range(int(sys.argv[1]),int(sys.argv[2]))]:
        p=seed if idx==-1 else bank[idx]
        status,w=solve(p,range(9),int(sys.argv[3]))
        print(json.dumps(dict(row=idx,status=status,witness=w)),flush=True)
        if w and len(w)>=193: break
