"""Piece-selection model for a fixed quotient walk inside a palette.
Q_n = Q_h x Q_k.  Visit i (cell c_i) selects exactly one directed induced
path of Q_h inside its allowed set (M u A for even cells, M u B for odd),
of size in [lo_i, hi_i], with entry/exit vertices in M.  Cross-visit
constraints are those of qmodel.QModel; no cycle cuts are needed."""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..', '..'))
_sys.path.insert(0, _HERE)

import sys, time, itertools
sys.path.insert(0, _os.path.join(REPO, 'milestones/21-snake-structure/scripts'))
from qmodel import check
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from pysat.formula import IDPool
def pc(x): return bin(x).count('1')
_cache = {}
def dpaths(allowed, h, maxlen):
    key = (frozenset(allowed), h, maxlen)
    if key in _cache: return _cache[key]
    al = 0
    for x in allowed: al |= 1 << x
    nbm = [sum(1 << (x ^ (1 << d)) for d in range(h)) for x in range(1 << h)]
    out = []
    def rec(path, used, blocked):
        out.append(tuple(path))
        if len(path) == maxlen: return
        cur = path[-1]
        for d in range(h):
            y = cur ^ (1 << d)
            if not (al >> y) & 1 or (blocked >> y) & 1: continue
            if nbm[y] & used & ~(1 << cur): continue
            path.append(y); rec(path, used | (1 << y), blocked | nbm[cur] | (1 << y)); path.pop()
    for s in sorted(allowed): rec([s], 1 << s, 1 << s)
    _cache[key] = out
    return out
class PModel:
    def __init__(self, h, k, walk, A, B, target, lo=1, hi=8, Mset=None, solver='cadical195', end_lo=1, end_hi=None):
        self.h, self.k, self.walk = h, k, list(walk)
        m = self.m = len(walk); H = 1 << h
        for a, b in zip(walk, walk[1:]): assert pc(a ^ b) == 1
        A = set(A); B = set(B); M = set(range(H)) - A - B if Mset is None else set(Mset)
        lo = lo if isinstance(lo, list) else [lo] * m
        hi = hi if isinstance(hi, list) else [hi] * m
        pool = IDPool(); cl = []
        y = self.y = [[pool.id(('y', i, x)) for x in range(H)] for i in range(m)]
        e = [[pool.id(('e', i, x)) for x in range(H)] for i in range(m - 1)]
        self.P = []
        for i, c in enumerate(walk):
            S = M | (A if pc(c) % 2 == 0 else B)
            cand = [p for p in dpaths(S, h, max(hi[i], 1)) if lo[i] <= len(p) <= hi[i]
                    and (i == 0 or p[0] in M) and (i == m - 1 or p[-1] in M)]
            pv = []
            for p in cand:
                v = pool.id(('p', i, p)); pv.append((v, p))
                for x in p: cl.append([-v, y[i][x]])
                if i > 0: cl.append([-v, e[i - 1][p[0]]])
                if i < m - 1: cl.append([-v, e[i][p[-1]]])
            self.P.append(pv)
            cl.append([v for v, _ in pv])
            cl.extend(CardEnc.atmost([v for v, _ in pv], 1, vpool=pool, encoding=EncType.seqcounter).clauses)
            byx = {x: [] for x in range(H)}
            for v, p in pv:
                for x in p: byx[x].append(v)
            for x in range(H): cl.append([-y[i][x]] + byx[x])
        for i in range(m - 1):
            cl.extend(CardEnc.atmost(e[i], 1, vpool=pool, encoding=EncType.pairwise).clauses)
        for i in range(m):
            for j in range(i + 1, m):
                d = pc(walk[i] ^ walk[j])
                if d == 0:
                    for x in range(H):
                        cl.append([-y[i][x], -y[j][x]])
                        for dd in range(h):
                            u = x ^ (1 << dd)
                            if u > x: cl.append([-y[i][x], -y[j][u]]); cl.append([-y[i][u], -y[j][x]])
                elif d == 1:
                    for x in range(H):
                        if j == i + 1: cl.append([-y[i][x], -y[j][x], e[i][x]])
                        else: cl.append([-y[i][x], -y[j][x]])
        self.nvars = sum(len(p) for p in self.P)
        self.solver = Solver(name=solver, bootstrap_with=cl)
        allv = [v for row in y for v in row]
        if target:
            enc = CardEnc.atleast(allv, target, vpool=pool, encoding=EncType.totalizer)
            self.solver.append_formula(enc.clauses)
    def solve(self, tlimit=60):
        t0 = time.time(); r = None
        while time.time() - t0 < tlimit:
            self.solver.conf_budget(20000); r = self.solver.solve_limited()
            if r is not None: break
        if r is None: return None, None
        if r is False: return False, None
        s = set(l for l in self.solver.get_model() if l > 0)
        path = []
        for i in range(self.m):
            ch = [p for v, p in self.P[i] if v in s]
            assert len(ch) == 1
            p = ch[0]
            if i > 0: assert p[0] == path_last
            q = p[1:] if i > 0 else p
            if i > 0: path.append((p[0] << self.k) | self.walk[i])
            path.extend((x << self.k) | self.walk[i] for x in q)
            path_last = p[-1]
        return True, path
def run(h, k, walk, A, B, target, tl=60, **kw):
    t = time.time(); Mo = PModel(h, k, walk, A, B, target, **kw); tb = time.time() - t
    r, p = Mo.solve(tl)
    out = dict(h=h, k=k, visits=len(walk), target=target, result={None: 'UNKNOWN', False: 'UNSAT', True: 'SAT'}[r],
               secs=round(time.time() - t, 1), build=round(tb, 1), pvars=Mo.nvars)
    if p: out['length'] = len(p); out['valid'] = check(p, h + k); out['path'] = p
    Mo.solver.delete()
    return out
