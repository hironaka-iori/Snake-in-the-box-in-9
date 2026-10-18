"""Local feasibility oracle for the empty-square-aware vertex weight (CP-SAT, decision only).

Weight of a selected vertex x in a snake S (all quantities local to the radius-3 ball):

    omega(x) = 21 * alpha(x) + sum_Q t(x, Q)

alpha(x) is the usual singleton-square count (unselected corners x ^ e_a ^ e_b with a, b not
the two path directions, 21 of them).  The sum runs over the squares Q = {c, c^e_a, c^e_b,
c^e_a^e_b} with c = x ^ e_k a neighbour of x off the path (k not a path direction, a, b != k)
that are EMPTY (no vertex of Q selected); such a Q gives 6/m where m is the number of selected
vertices of its parallel square P = Q ^ e_k = {x, x^e_a, x^e_b, x^e_a^e_b} (m is 1, 2 or 3, so
t = 6, 3 or 2).  An empty square has seven parallel squares and hands out at most 1/7 to each,
so sum_x sum_Q 6/m <= 42 * s0 and  sum_x omega(x) <= 21 * (T + 2 s0) = 21 * (9214 - 35 v).

A bucket query asks whether there is a local configuration with 21*b <= omega(c) <= 21*b + 20
at every centre c (top bucket open above).  INFEASIBLE means the window is excluded; FEASIBLE
or UNKNOWN count as allowed, so the automaton stays an over-approximation.

  python omega_oracle.py --dirs 0 1 2 3 --buckets 4 4 4
"""
import argparse, itertools, time
from itertools import combinations
from ortools.sat.python import cp_model

from wincert import window_from_dirs, cycles_of


class OmegaModel:
    def __init__(self, dirs, radius=3, ends=2):
        self.window = window_from_dirs(dirs)
        self.centers = self.window[1:-1]
        self.radius = radius
        ball = [v for v in range(512) if min((v ^ c).bit_count() for c in self.centers) <= radius]
        self.ball, self.B = ball, set(ball)
        m = cp_model.CpModel(); self.m = m
        X = {v: m.NewBoolVar(f'x{v}') for v in ball}; self.X = X
        for v in self.window:
            m.Add(X[v] == 1)
        endvars = []
        for v in ball:
            ns = [X[v ^ 1 << k] for k in range(9) if v ^ 1 << k in self.B]
            m.Add(sum(ns) <= 2).OnlyEnforceIf(X[v])
            if len(ns) == 9:
                e = m.NewBoolVar(f'e{v}'); endvars.append(e)
                m.Add(sum(ns) >= 1).OnlyEnforceIf(X[v])
                m.AddImplication(e, X[v])
                # selected with <= 1 selected neighbour  ->  endpoint
                m.Add(sum(ns) >= 2).OnlyEnforceIf([X[v], e.Not()])
                m.Add(sum(ns) <= 1).OnlyEnforceIf(e)
        m.Add(sum(endvars) <= ends)
        # no full square, no 6-cycle of a 3-cube inside the ball
        for v in ball:
            for a, b in combinations(range(9), 2):
                if v >> a & 1 or v >> b & 1:
                    continue
                sq = [v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b]
                if all(w in self.B for w in sq):
                    m.AddBoolOr([X[w].Not() for w in sq])
            for t in combinations(range(9), 3):
                if any(v >> k & 1 for k in t):
                    continue
                cube = [v ^ sum(1 << t[j] for j in range(3) if r >> j & 1) for r in range(8)]
                if all(w in self.B for w in cube):
                    for r in range(4):
                        m.AddBoolOr([X[cube[s]].Not() for s in range(8) if s not in (r, 7 - r)])
        # omega per centre
        self.omega = {}
        self.alpha = {}
        for i, c in enumerate(self.centers, 1):
            used = {(c ^ self.window[i - 1]).bit_length() - 1, (c ^ self.window[i + 1]).bit_length() - 1}
            free = [d for d in range(9) if d not in used]
            corners = [X[c ^ 1 << a ^ 1 << b] for a, b in combinations(free, 2)]
            assert len(corners) == 21
            alpha = sum(1 - z for z in corners)
            self.alpha[c] = alpha
            shares = []
            for k in free:
                y = c ^ 1 << k
                for a, b in combinations([d for d in range(9) if d != k], 2):
                    Q = [y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b]
                    P_others = [c ^ 1 << a, c ^ 1 << b, c ^ 1 << a ^ 1 << b]
                    assert all(w in self.B for w in Q + P_others), (c, Q)
                    E = m.NewBoolVar('')
                    for w in Q:
                        m.AddImplication(E, X[w].Not())
                    m.AddBoolOr([E] + [X[w] for w in Q])
                    s = sum(X[w] for w in P_others)
                    z0 = m.NewBoolVar(''); z1 = m.NewBoolVar('')
                    m.Add(s == 0).OnlyEnforceIf(z0); m.Add(s >= 1).OnlyEnforceIf(z0.Not())
                    m.Add(s <= 1).OnlyEnforceIf(z1); m.Add(s >= 2).OnlyEnforceIf(z1.Not())
                    t = m.NewIntVar(0, 6, '')
                    # t = E * (2 + [s<=1] + 3 [s==0])
                    g2 = E
                    g1 = m.NewBoolVar(''); m.AddBoolAnd([E, z1]).OnlyEnforceIf(g1); m.AddBoolOr([E.Not(), z1.Not(), g1])
                    g3 = m.NewBoolVar(''); m.AddBoolAnd([E, z0]).OnlyEnforceIf(g3); m.AddBoolOr([E.Not(), z0.Not(), g3])
                    m.Add(t == 2 * g2 + g1 + 3 * g3)
                    shares.append(t)
            assert len(shares) == 196, len(shares)
            self.omega[c] = 21 * alpha + sum(shares)

    def constrain_buckets(self, buckets, cap):
        """21*b <= omega <= 21*b + 20 per centre; the top bucket b == cap is open above."""
        for c, b in zip(self.centers, buckets):
            self.m.Add(self.omega[c] >= 21 * b)
            if b < cap:
                self.m.Add(self.omega[c] <= 21 * b + 20)

    def constrain_alpha(self, alphas):
        for c, a in zip(self.centers, alphas):
            if a is None:
                continue
            lo, hi = a if isinstance(a, tuple) else (a, a)
            self.m.Add(self.alpha[c] >= lo); self.m.Add(self.alpha[c] <= hi)

    def decide(self, time_limit=60.0, max_rounds=10000):
        solver = cp_model.CpSolver()
        solver.parameters.max_time_in_seconds = time_limit
        solver.parameters.num_workers = 1
        cuts = 0
        t0 = time.time()
        while True:
            st = solver.Solve(self.m)
            if st == cp_model.INFEASIBLE:
                return 'UNSAT', None, cuts
            if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
                return 'UNKNOWN', None, cuts
            sel = [v for v in self.ball if solver.Value(self.X[v])]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', sel, cuts
            for cy in cyc:
                self.m.AddBoolOr([self.X[w].Not() for w in cy]); cuts += 1
            if cuts > max_rounds or time.time() - t0 > time_limit:
                return 'UNKNOWN', None, cuts


def omega_of(S, x):
    """Exact omega(x) for a selected vertex x of an induced path S (for controls)."""
    S = set(S)
    used = {(x ^ y).bit_length() - 1 for y in (x ^ 1 << k for k in range(9)) if y in S}
    free = [d for d in range(9) if d not in used]
    alpha = sum(1 for a, b in combinations(free, 2) if (x ^ 1 << a ^ 1 << b) not in S)
    share = 0
    for k in free:
        y = x ^ 1 << k
        for a, b in combinations([d for d in range(9) if d != k], 2):
            Q = [y, y ^ 1 << a, y ^ 1 << b, y ^ 1 << a ^ 1 << b]
            if any(w in S for w in Q):
                continue
            mcount = 1 + sum(1 for w in (x ^ 1 << a, x ^ 1 << b, x ^ 1 << a ^ 1 << b) if w in S)
            share += 6 // mcount if mcount in (1, 2, 3) else 0
    return 21 * alpha + share


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--dirs', type=int, nargs='+', required=True)
    ap.add_argument('--buckets', type=int, nargs='+', required=True)
    ap.add_argument('--cap', type=int, default=12)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--time', type=float, default=60.0)
    a = ap.parse_args()
    t = time.time()
    M = OmegaModel(a.dirs, a.radius)
    M.constrain_buckets(a.buckets, a.cap)
    st, sel, cuts = M.decide(a.time)
    print(st, 'cuts', cuts, 'ball', len(M.ball), f'{time.time() - t:.1f}s')
