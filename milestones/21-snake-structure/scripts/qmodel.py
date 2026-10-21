"""Quotient-walk model.

Q_n = Q_h (heavy) x Q_k (light).  A snake whose light transitions follow a
fixed walk c_0, c_1, ..., c_{m-1} in Q_k (the 'quotient walk') splits into m
pieces; piece i is an induced path of Q_h inside cell c_i, entered at e_i and
left at f_i = e_{i+1}.  This model fixes ONLY the quotient walk; all heavy
coordinates are free.  It is exact for that family:

  * y[i][x]: heavy vertex x is on piece i (Q_n vertex (x, c_i));
  * selected x in piece i: (#selected Q_h nbrs in piece i) + e_i(x) + f_i(x) = 2
    (e_0 / f_{m-1} are the global ends, exactly one vertex each);
  * same cell, i != j: contents disjoint and non-adjacent;
  * adjacent cells, |i-j| >= 2: contents disjoint;
  * consecutive pieces share only x = f_i;
  * remaining cycles inside one piece are removed lazily.
"""
import os as _os, sys as _sys
_HERE = _os.path.dirname(_os.path.abspath(__file__))
REPO = _os.path.abspath(_os.path.join(_HERE, '..', '..', '..'))
_sys.path.insert(0, _HERE)

import itertools, sys, time
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
from pysat.formula import IDPool

def pc(x): return bin(x).count('1')

class QModel:
    def __init__(self, h, k, walk, target=None, fix_start=True, minsize=None, maxsize=None,
                 solver='cd19', extra_cnf=None, allowed=None, bnd_allowed=None, grow=None):
        self.h, self.k, self.walk = h, k, list(walk)
        m = self.m = len(walk)
        for a, b in zip(walk, walk[1:]):
            assert pc(a ^ b) == 1, walk
        H = 1 << h
        pool = self.pool = IDPool()
        y = self.y = [[pool.id(('y', i, x)) for x in range(H)] for i in range(m)]
        # boundary variables: bnd[i][x] is the vertex where piece i-1 -> piece i (i=1..m-1)
        # bnd[0] = start, bnd[m] = end
        bnd = self.bnd = [[pool.id(('b', i, x)) for x in range(H)] for i in range(m + 1)]
        cl = self.cl = []
        for i in range(m + 1):
            lits = bnd[i]
            cl.extend(CardEnc.equals(lits, 1, vpool=pool, encoding=EncType.seqcounter).clauses)
        for i in range(m):
            for x in range(H):
                cl.append([-bnd[i][x], y[i][x]])
                cl.append([-bnd[i + 1][x], y[i][x]])
            for x in range(1, m and H):
                pass
        for i in range(1, m):
            for x in range(H):
                cl.append([-bnd[i][x], y[i - 1][x]])
        if fix_start:
            cl.append([bnd[0][0]])
        # degree: selected => exactly 2 among nbrs-in-piece + bnd[i] + bnd[i+1]
        for i in range(m):
            for x in range(H):
                lits = [y[i][x ^ (1 << d)] for d in range(h)] + [bnd[i][x], bnd[i + 1][x]]
                n = len(lits)
                for tri in itertools.combinations(lits, 3):
                    cl.append([-y[i][x]] + [-t for t in tri])
                for j in range(n):
                    cl.append([-y[i][x]] + [lits[t] for t in range(n) if t != j])
        # cross-piece constraints
        for i in range(m):
            for j in range(i + 1, m):
                d = pc(walk[i] ^ walk[j])
                if d == 0:
                    for x in range(H):
                        cl.append([-y[i][x], -y[j][x]])
                        for dd in range(h):
                            u = x ^ (1 << dd)
                            cl.append([-y[i][x], -y[j][u]])
                elif d == 1:
                    for x in range(H):
                        if j == i + 1:
                            cl.append([-y[i][x], -y[j][x], bnd[j][x]])
                        else:
                            cl.append([-y[i][x], -y[j][x]])
        # small cycle cuts: squares and induced hexagons of every Q3 of Q_h
        for i in range(m):
            for dims in itertools.combinations(range(h), 2):
                msk = sum(1 << d for d in dims)
                for base in range(H):
                    if base & msk: continue
                    sq = [base, base | (1 << dims[0]), base | msk, base | (1 << dims[1])]
                    cl.append([-y[i][v] for v in sq])
            if h >= 3:
                for dims in itertools.combinations(range(h), 3):
                    msk = sum(1 << d for d in dims)
                    sub = [sum(((s >> t) & 1) << dims[t] for t in range(3)) for s in range(8)]
                    for base in range(H):
                        if base & msk: continue
                        for a in range(4):
                            hexv = [base | sub[s] for s in range(8) if s != a and s != 7 - a]
                            cl.append([-y[i][v] for v in hexv])
        if minsize:
            for i, ms in minsize.items():
                cl.extend([c for c in CardEnc.atleast(y[i], ms, vpool=pool, encoding=EncType.seqcounter).clauses])
        if maxsize:
            for i, ms in maxsize.items():
                cl.extend([c for c in CardEnc.atmost(y[i], ms, vpool=pool, encoding=EncType.seqcounter).clauses])
        if allowed is not None:
            for i in range(m):
                for x in range(H):
                    if x not in allowed[i]: cl.append([-y[i][x]])
        if bnd_allowed is not None:
            for i in range(1, m):
                for x in range(H):
                    if x not in bnd_allowed: cl.append([-bnd[i][x]])
        if grow is not None:
            gs = []
            for i, ms in grow.items():
                g = pool.id(('g', i)); gs.append(g)
                for c in CardEnc.atleast(y[i], ms + 1, vpool=pool, encoding=EncType.seqcounter).clauses:
                    cl.append([-g] + c)
            cl.append(gs)
        allv = [v for row in y for v in row]
        self.allv = allv
        self.solver = Solver(name=solver, bootstrap_with=cl)
        self.total = None
        if target is not None:
            enc = CardEnc.atleast(allv, target, vpool=pool, encoding=EncType.totalizer)
            self.solver.append_formula(enc.clauses)
        self.cuts = 0

    def decode(self, model):
        s = set(l for l in model if l > 0)
        H = 1 << self.h
        pieces = [[x for x in range(H) if self.y[i][x] in s] for i in range(self.m)]
        bnd = [[x for x in range(H) if self.bnd[i][x] in s][0] for i in range(self.m + 1)]
        return pieces, bnd

    def order(self, piece, a, b):
        S = set(piece)
        if a == b: return [a]
        out = [a]; prev = None; cur = a
        while cur != b:
            nb = [cur ^ (1 << d) for d in range(self.h) if (cur ^ (1 << d)) in S and (cur ^ (1 << d)) != prev]
            if len(nb) != 1: return None
            prev, cur = cur, nb[0]; out.append(cur)
        return out

    def solve(self, tlimit=60, budget=20000):
        t0 = time.time()
        while True:
            self.solver.conf_budget(budget)
            r = self.solver.solve_limited()
            if r is None:
                if time.time() - t0 > tlimit: return None, None
                continue
            if r is False: return False, None
            pieces, bnd = self.decode(self.solver.get_model())
            path = []; added = False
            for i, pce in enumerate(pieces):
                seq = self.order(pce, bnd[i], bnd[i + 1])
                if seq is None or len(seq) != len(pce):
                    S = set(pce) - set(seq or [])
                    # each remaining component is a cycle: cut it
                    while S:
                        st = S.pop(); comp = {st}; stack = [st]
                        while stack:
                            u = stack.pop()
                            for d in range(self.h):
                                w = u ^ (1 << d)
                                if w in S: S.discard(w); comp.add(w); stack.append(w)
                        self.solver.add_clause([-self.y[i][v] for v in comp])
                        self.cuts += 1; added = True
                else:
                    path.extend([(x << self.k) | self.walk[i] for x in seq])
            if not added:
                return True, path
            if time.time() - t0 > tlimit: return None, None

def check(path, n):
    pos = {}
    for i, v in enumerate(path):
        if v in pos: return False
        pos[v] = i
    for i, v in enumerate(path):
        if i and pc(v ^ path[i - 1]) != 1: return False
        for d in range(n):
            j = pos.get(v ^ (1 << d))
            if j is not None and abs(j - i) > 1: return False
    return True
