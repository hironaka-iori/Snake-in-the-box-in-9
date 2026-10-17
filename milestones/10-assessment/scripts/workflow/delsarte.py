"""Distance-distribution (Delsarte) LP for a snake's vertex set in Q9.
B_i = #ordered pairs at Hamming distance i. B_0=v, B_1=2(v-1), B_2 = 23v+10-T (checked on bank),
sum B_i = v^2, Krawtchouk transforms >= 0, B_3 >= 2(v-3).  T in [c*v (+const), 9214-35v] (n0 >= 0).
Question: for which v is this feasible?  Compare with the square identity alone: v <= 9214/(35+c)."""
import sys
from math import comb
from ortools.linear_solver import pywraplp

n = 9
def K(j, i):
    return sum((-1) ** s * comb(i, s) * comb(n - i, j - s) for s in range(0, j + 1))

def feasible(v, c, const=0.0, extra=True):
    s = pywraplp.Solver.CreateSolver('GLOP')
    B = [s.NumVar(0, s.infinity(), f'B{i}') for i in range(n + 1)]
    T = s.NumVar(0, s.infinity(), 'T')
    s.Add(B[0] == v); s.Add(B[1] == 2 * (v - 1))
    s.Add(B[2] == 23 * v + 10 - T)
    s.Add(sum(B) == v * v)
    for j in range(n + 1):
        s.Add(sum(B[i] * K(j, i) for i in range(n + 1)) >= 0)
    s.Add(T >= c * v + const)
    s.Add(T <= 9214 - 35 * v)
    if extra:
        s.Add(B[3] >= 2 * (v - 3))
    st = s.Solve()
    return st == pywraplp.Solver.OPTIMAL

if __name__ == '__main__':
    from fractions import Fraction
    for c, const in [(1, 0), (Fraction(7, 3), Fraction(5, 3)), (Fraction(14, 5), 0), (3, 0), (4, 0), (6, 0), (8.5, 0), (10, 0), (12, 0)]:
        vmax = max([v for v in range(2, 300) if feasible(v, float(c), float(const))], default=None)
        print(f'T >= {c} v + {const}: Delsarte+identity LP max feasible v = {vmax};  square identity alone: v <= {int(9214 / (35 + float(c)))}')
    # Delsarte with no T information at all except T <= 9214-35v and T>=0
    vmax = max([v for v in range(2, 600) if feasible(v, 0.0, 0.0)], default=None)
    print('T >= 0 only:', vmax)
