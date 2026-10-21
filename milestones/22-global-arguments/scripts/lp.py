"""Tiny exact LP solver (two-phase simplex, Bland's rule, Fractions).

solve(c, A_ub, b_ub, A_eq, b_eq) maximises c.x subject to A_ub x <= b_ub,
A_eq x = b_eq, x >= 0.  Returns (status, value, x) with status in
{'optimal', 'infeasible', 'unbounded'}.  Intended for LPs with tens of
variables (Delsarte-type bounds); everything is exact rational arithmetic.
"""
from fractions import Fraction as F


def solve(c, A_ub=(), b_ub=(), A_eq=(), b_eq=()):
    n = len(c)
    rows = []  # (coeffs over structural+slack, rhs)
    A_ub = [list(map(F, r)) for r in A_ub]
    A_eq = [list(map(F, r)) for r in A_eq]
    b_ub = list(map(F, b_ub))
    b_eq = list(map(F, b_eq))
    m_ub, m_eq = len(A_ub), len(A_eq)
    ns = n + m_ub  # structural + slacks
    for i, r in enumerate(A_ub):
        row = r + [F(0)] * m_ub
        row[n + i] = F(1)
        rows.append([row, b_ub[i]])
    for i, r in enumerate(A_eq):
        rows.append([r + [F(0)] * m_ub, b_eq[i]])
    # make rhs >= 0
    for rw in rows:
        if rw[1] < 0:
            rw[0] = [-a for a in rw[0]]
            rw[1] = -rw[1]
    m = len(rows)
    # artificials for every row (simple, robust)
    N = ns + m
    T = []
    for i, (row, rhs) in enumerate(rows):
        art = [F(0)] * m
        art[i] = F(1)
        T.append(row + art + [rhs])
    basis = [ns + i for i in range(m)]

    def pivot(r, col):
        pv = T[r][col]
        T[r] = [a / pv for a in T[r]]
        for i in range(m):
            if i != r and T[i][col] != 0:
                f = T[i][col]
                Ti, Tr = T[i], T[r]
                T[i] = [a - f * b for a, b in zip(Ti, Tr)]
        basis[r] = col

    def run(obj, allowed):
        # obj: list of length N (maximise). returns 'optimal'/'unbounded'
        while True:
            # reduced costs
            best = None
            for j in range(N):
                if not allowed[j] or j in basis:
                    continue
                rc = obj[j] - sum(obj[basis[i]] * T[i][j] for i in range(m))
                if rc > 0:
                    best = j
                    break  # Bland
            if best is None:
                return 'optimal'
            col = best
            r, ratio = None, None
            for i in range(m):
                if T[i][col] > 0:
                    q = T[i][-1] / T[i][col]
                    if ratio is None or q < ratio or (q == ratio and basis[i] < basis[r]):
                        r, ratio = i, q
            if r is None:
                return 'unbounded'
            pivot(r, col)

    obj1 = [F(0)] * ns + [F(-1)] * m
    run(obj1, [True] * N)
    if sum(T[i][-1] for i in range(m) if basis[i] >= ns) > 0:
        return 'infeasible', None, None
    # drive artificials out of basis
    for i in range(m):
        if basis[i] >= ns:
            for j in range(ns):
                if T[i][j] != 0:
                    pivot(i, j)
                    break
    allowed = [True] * ns + [False] * m
    obj2 = [F(x) for x in c] + [F(0)] * (N - n)
    st = run(obj2, allowed)
    if st == 'unbounded':
        return 'unbounded', None, None
    x = [F(0)] * N
    for i in range(m):
        x[basis[i]] = T[i][-1]
    val = sum(F(c[j]) * x[j] for j in range(n))
    return 'optimal', val, x[:n]


if __name__ == '__main__':
    # max x+y s.t. x+2y<=4, 3x+y<=6
    print(solve([1, 1], [[1, 2], [3, 1]], [4, 6]))
