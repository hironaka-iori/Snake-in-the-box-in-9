"""Retry fixed projected walks using carry-save counters and CaDiCaL."""
import json
import sys
from itertools import combinations, product
from collections import defaultdict
from pysat.solvers import Cadical195
import search_q9_fiber_port_scores as lift


class CounterSolver(Cadical195):
    def __init__(self):
        super().__init__()
        self.pending = []

    def add_atmost(self, lits, k):
        if k == 1:
            for a, b in combinations(lits, 2):
                self.add_clause([-a,-b])
        else:
            self.pending.append((lits, k))

    def solve_limited(self):
        next_var = self.nof_vars() + 1
        for literals, k in self.pending:
            groups = defaultdict(list)
            groups[0] = list(literals)
            bits = []
            i = 0
            while groups[i]:
                col = groups[i]
                while len(col) > 1:
                    n = min(3,len(col))
                    inputs = [col.pop() for _ in range(n)]
                    low, high = next_var, next_var+1
                    next_var += 2
                    for vals in product([0,1], repeat=n):
                        prefix = [-v if b else v for v,b in zip(inputs,vals)]
                        self.add_clause(prefix + [low if sum(vals)%2 else -low])
                        self.add_clause(prefix + [high if sum(vals)>=2 else -high])
                    col.append(low)
                    groups[i+1].append(high)
                bits.append(col.pop())
                i += 1
            for j,x in enumerate(bits):
                if (k>>j)&1 == 0:
                    self.add_clause([-x]+[-bits[h] if (k>>h)&1 else bits[h] for h in range(j+1,len(bits))])
        self.pending.clear()
        return super().solve_limited()


def test():
    for n in range(2,9):
        for k in range(n):
            with CounterSolver() as s:
                xs=[(-1 if j%2 else 1)*j for j in range(1,n+1)]
                s.add_clause([n,-n])
                s.add_atmost(xs,k)
                s.solve_limited()
                for vals in product([0,1],repeat=n):
                    assert s.solve(assumptions=[v if b else -v for v,b in zip(xs,vals)])==(sum(vals)<=k)


if __name__=='__main__':
    test()
    lift.Minicard = CounterSolver
    data=json.load(open('q9_lift_frontier.json'))
    starts=[bytes.fromhex(s) for s in data['three_axes_from_records']['unresolved']]
    todo=set(starts)
    hints={}
    for ln in open('/private/tmp/q9_project_records_input9'):
        _,*steps=map(int,ln.split())
        for p,h in lift.projections(steps,3):
            if p in todo:hints[p]=h
    for p in starts:
        status,w=lift.fiber_solve(p,3,int(sys.argv[1]),int(sys.argv[2]),hints[p])
        print(json.dumps([status,p.hex(),w]),flush=True)
        if w:break
