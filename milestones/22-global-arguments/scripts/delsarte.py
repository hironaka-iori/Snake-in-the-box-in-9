"""Delsarte LP for snakes (induced paths) in Q_n.

For a snake S with v vertices let A_i = (1/v) #{(x,y) in S^2 : d(x,y) = i}.
Then A_0 = 1, A_1 = 2(v-1)/v, sum A_i = v, and the Krawtchouk (MacWilliams)
inequalities sum_i A_i K_k(i) >= 0 hold for every k.  The square identity is
linear in A_2:
    D2 = v A_2 / 2  (distance-2 pairs),
    s0 = N - C(n,2) v + (n-1)(v-1) - (v-2) + D2        (empty squares)  >= 0
    T  = C(n,2) v - 2(n-1)(v-1) - 2 D2 + 3(v-2)         (singleton squares)
For each v we report the range of A_2 allowed by Delsarte alone, compared with
the range allowed by s0 >= 0 and T >= mu v, and the largest feasible v.
"""
import sys
from fractions import Fraction as F
from math import comb
from lp import solve


def K(n, k, i):
    return sum((-1) ** j * comb(i, j) * comb(n - i, k - j) for j in range(k + 1))


def model(n, v, mu=None, use_delsarte=True, use_s0=True, extra=None):
    v = F(v)
    N = comb(n, 2) * 2 ** (n - 2)
    # variables A_1..A_n
    A_eq, b_eq, A_ub, b_ub = [], [], [], []
    r = [F(0)] * n; r[0] = F(1); A_eq.append(r); b_eq.append(2 * (v - 1) / v)
    A_eq.append([F(1)] * n); b_eq.append(v - 1)
    if use_delsarte:
        for k in range(1, n + 1):
            # -sum_{i>=1} A_i K_k(i) <= K_k(0)
            A_ub.append([-F(K(n, k, i)) for i in range(1, n + 1)])
            b_ub.append(F(K(n, k, 0)))
    if use_s0:
        # s0 >= 0  <=>  -v/2 A_2 <= N - C(n,2)v + (n-1)(v-1) - (v-2)
        r = [F(0)] * n; r[1] = -v / 2
        A_ub.append(r); b_ub.append(N - comb(n, 2) * v + (n - 1) * (v - 1) - (v - 2))
    if mu is not None:
        # T >= mu v  <=>  v A_2 <= C(n,2)v - 2(n-1)(v-1) + 3(v-2) - mu v
        r = [F(0)] * n; r[1] = v
        A_ub.append(r); b_ub.append(comb(n, 2) * v - 2 * (n - 1) * (v - 1) + 3 * (v - 2) - F(mu) * v)
    if extra:
        for (row, rhs) in extra(v):
            A_ub.append(row); b_ub.append(rhs)
    return A_ub, b_ub, A_eq, b_eq


def a2range(n, v, **kw):
    A_ub, b_ub, A_eq, b_eq = model(n, v, **kw)
    c = [F(0)] * n; c[1] = F(1)
    st, hi, _ = solve(c, A_ub, b_ub, A_eq, b_eq)
    if st == 'infeasible':
        return None
    c[1] = F(-1)
    st, lo, _ = solve(c, A_ub, b_ub, A_eq, b_eq)
    return (-lo, hi)


def maxv(n, **kw):
    best = None
    for v in range(2, 2 ** (n - 1) + 2):
        if a2range(n, v, **kw) is not None:
            best = v
    return best


if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for v in ([200, 220, 230, 238, 240, 245, 250, 256] if n == 9 else range(2 ** (n - 2), 2 ** (n - 1) + 1, 2)):
        d = a2range(n, v, use_s0=False)
        s = a2range(n, v, use_delsarte=False)
        b = a2range(n, v)
        f = lambda r: None if r is None else (round(float(r[0]), 3), round(float(r[1]), 3))
        print(n, v, 'delsarte', f(d), 's0', f(s), 'both', f(b))
