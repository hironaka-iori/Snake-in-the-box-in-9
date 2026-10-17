import sys
from math import comb
from ortools.linear_solver import pywraplp
from delsarte import K
n=9
def maxT(v, extra=True):
    s = pywraplp.Solver.CreateSolver('GLOP')
    B = [s.NumVar(0, s.infinity(), f'B{i}') for i in range(n + 1)]
    T = s.NumVar(0, s.infinity(), 'T')
    s.Add(B[0] == v); s.Add(B[1] == 2 * (v - 1)); s.Add(B[2] == 23 * v + 10 - T); s.Add(sum(B) == v * v)
    for j in range(n + 1):
        s.Add(sum(B[i] * K(j, i) for i in range(n + 1)) >= 0)
    if extra: s.Add(B[3] >= 2 * (v - 3))
    s.Maximize(T)
    st = s.Solve()
    return T.solution_value() if st == pywraplp.Solver.OPTIMAL else None
print(' v   Delsarte maxT  T/v    | square-identity maxT=9214-35v  T/v')
for v in [150,170,180,185,190,192,194,196,198,200,205,210,215,220,230,240,246]:
    t=maxT(v); q=9214-35*v
    print('%4d  %10.1f  %6.3f   | %6d  %6.3f   binding:%s'%(v,t,t/v,q,q/v,'Delsarte' if t<q else 'square'))
