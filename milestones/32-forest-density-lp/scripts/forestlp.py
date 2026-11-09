"""Local density LP for induced linear forests in Q_n, using labelled k-subcube patterns.

Variables x_tau >= 0: the fraction of the C(n,k) 2^(n-k) k-subcubes Q whose labelled pattern
(F cap Q with GLOBAL degrees, see patterns.py) is of type tau.  For every induced linear forest
F in Q_n with at most c paths these hold:

  (1) sum_tau x_tau = 1;
  (2) |F|/2^n = sum_tau x_tau |A_tau|/2^k               (each vertex is in C(n,k) subcubes);
  (3) sum_tau x_tau e_tau/2^k <= 2c/2^n, e_tau = sum_{v in A_tau} (2 - l(v))
      (sum over F of (2 - deg) = 2 * #paths);
  (4) face consistency, for every j < k, every labelled j-pattern sigma, every position p of
      sigma with v in F, and gamma in {0,1,2}:
        sum_tau x_tau sum_{j-faces R of tau, isos g: R -> sigma} ([gain(g^-1 p) = gamma] - P(gamma|o_p)) = 0,
      where gain = (degree in Q) - (degree in R), o_p = l(p) - ld_sigma(p) is the number of
      F-neighbours of the vertex outside R, and P(gamma|o) = C(o,gamma) C(n-j-o, k-j-gamma) / C(n-j, k-j)
      is the exact fraction of the C(n-j, k-j) k-subcubes Q containing R in which the vertex
      gains gamma neighbours.  (Summing over all pairs (R, Q) with R a j-face of Q.)

Maximising (2) subject to (1), (3), (4) bounds |F|/2^n.  Any dual vector gives a rigorous bound
  |F|/2^n <= max_tau [ |A_tau|/2^k - yE e_tau/2^k - sum_r y_r M[r, tau] ] + yE * 2c/2^n   (yE >= 0),
which `certify` evaluates exactly with fractions.
"""
import sys
from fractions import Fraction
from math import comb as _comb


def comb(a, b):
    return _comb(a, b) if 0 <= b <= a else 0
import numpy as np
import highspy
from patterns import patterns, out_feasible, local_degrees


def face_maps(k, j):
    """list of j-faces of Q_k, each as the list of Q_k vertices in Q_j order."""
    out = []
    for J in __import__('itertools').combinations(range(k), j):
        rest = [i for i in range(k) if i not in J]
        for s in range(1 << len(rest)):
            base = 0
            for b, i in enumerate(rest):
                if s >> b & 1:
                    base |= 1 << i
            verts = []
            for u in range(1 << j):
                v = base
                for b, i in enumerate(J):
                    if u >> b & 1:
                        v |= 1 << i
                verts.append(v)
            out.append(verts)
    return out


def build(n, k, levels=None):
    P = patterns(k)
    reps = [t for t in P.reps if out_feasible(k, t, n - k)]
    V = 1 << k
    levels = range(k) if levels is None else levels
    rows = {}           # (j, sigma, p, gamma) -> row index
    cols = []           # per tau: dict row -> coefficient (Fraction)
    canon_cache = {}
    for t in reps:
        A = [v for v in range(V) if t[v]]
        ldQ = local_degrees(k, A)
        coef = {}
        for j in levels:
            Pj = patterns(j)
            Vj = 1 << j
            denom = comb(n - j, k - j)
            for verts in face_maps(k, j):
                tR = tuple(t[v] for v in verts)
                if tR not in canon_cache:
                    canon_cache[tR] = Pj.canon(tR)
                sig, gs = canon_cache[tR]
                Asig = [u for u in range(Vj) if sig[u]]
                ldS = local_degrees(j, Asig)
                for g in gs:
                    inv = [0] * Vj
                    for u in range(Vj):
                        inv[g[u]] = u
                    for p in Asig:
                        v = verts[inv[p]]
                        o = sig[p] - 1 - ldS[p]
                        gain = ldQ[v] - ldS[p]
                        for gam in range(3):
                            pr = Fraction(comb(o, gam) * comb(n - j - o, k - j - gam), denom)
                            val = (1 if gain == gam else 0) - pr
                            if val:
                                key = (j, sig, p, gam)
                                coef[key] = coef.get(key, 0) + val
        for key in coef:
            if key not in rows:
                rows[key] = len(rows)
        cols.append({rows[key]: val for key, val in coef.items() if val})
    obj = [Fraction(sum(1 for x in t if x), V) for t in reps]
    end = [Fraction(sum(3 - x for x in t if x), V) for t in reps]
    return dict(n=n, k=k, reps=reps, rows=rows, cols=cols, obj=obj, end=end)


def solve(M, eps, extra=None):
    """max density subject to (1),(3) with 2c/2^n = eps, (4).  Returns (value, duals)."""
    reps, cols, nr = M['reps'], M['cols'], len(M['rows'])
    N = len(reps)
    h = highspy.Highs()
    h.setOptionValue('output_flag', False)
    h.setOptionValue('threads', 1)
    inf = highspy.kHighsInf
    lp = highspy.HighsLp()
    lp.num_col_ = N
    lp.num_row_ = nr + 2
    lp.col_cost_ = np.array([-float(x) for x in M['obj']])
    lp.col_lower_ = np.zeros(N)
    lp.col_upper_ = np.full(N, inf)
    lo = np.zeros(nr + 2)
    up = np.zeros(nr + 2)
    lo[nr], up[nr] = 1, 1             # sum x = 1
    lo[nr + 1], up[nr + 1] = -inf, eps  # endpoint density
    lp.row_lower_ = lo
    lp.row_upper_ = up
    starts, idx, vals = [0], [], []
    for i, cdict in enumerate(cols):
        for r, v in sorted(cdict.items()):
            idx.append(r)
            vals.append(float(v))
        idx.append(nr)
        vals.append(1.0)
        if M['end'][i]:
            idx.append(nr + 1)
            vals.append(float(M['end'][i]))
        starts.append(len(idx))
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.array(starts)
    lp.a_matrix_.index_ = np.array(idx)
    lp.a_matrix_.value_ = np.array(vals)
    h.passModel(lp)
    h.run()
    sol = h.getSolution()
    val = -h.getInfo().objective_function_value
    rd = np.array(sol.row_dual)
    return val, rd, np.array(sol.col_value)


def certify(M, rd, eps_list, den=10**6):
    """Exact bound from rounded duals: returns {eps: Fraction bound}.  Valid for every eps with
    yE >= 0 (sign convention of HiGHS for a minimisation of -obj: row duals y, we use -y)."""
    nr = len(M['rows'])
    y = [-Fraction(float(v)).limit_denominator(den) for v in rd[:nr]]
    yE = -Fraction(float(rd[nr + 1])).limit_denominator(den)
    if yE < 0:
        yE = Fraction(0)
    worst = None
    for i in range(len(M['reps'])):
        s = M['obj'][i] - yE * M['end'][i] - sum(y[r] * v for r, v in M['cols'][i].items())
        if worst is None or s > worst:
            worst = s
    return {e: worst + yE * Fraction(e) for e in eps_list}, yE, worst


if __name__ == '__main__':
    n, k = int(sys.argv[1]), int(sys.argv[2])
    M = build(n, k)
    print('n=%d k=%d: %d patterns, %d consistency rows' % (n, k, len(M['reps']), len(M['rows'])))
    for c in range(0, 2 ** (n - 2) + 1):
        eps = 2 * c / 2 ** n
        val, rd, x = solve(M, eps)
        print('c=%2d  LP |F| <= %.4f' % (c, val * 2 ** n))
