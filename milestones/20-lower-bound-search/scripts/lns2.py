"""Round 2: stronger CNF for large-neighbourhood repair of Q9 snakes.

Same search space as lns.Model (kept vertices fixed, free vertices chosen,
selected degree 1..2, exactly two endpoints, at least `target` selected,
lazy cuts on cycle components), plus redundant constraints that every
induced path in Q9 satisfies:

* colour balance: Q9 is bipartite, so the two colour classes of a path
  differ in size by at most one (full totalizers on each colour, linked);
* hexagon cuts: no induced 6-cycle (all 6-cycles of Q9 lie in a Q3);
  with the square cuts this is "at most 5 of the 8 vertices of every Q3";
* subcube capacity: the trace of an induced path on a k-subcube is an
  induced linear forest; its maximum size is 5, 8, 16, 32 for k = 3..6
  (checked exhaustively for k <= 4 and by SAT with cycle cuts for k = 5, 6,
  see capq.py).  We add "at most 8 of every Q4" and optionally
  "at most 16 of every Q5".

Solver: CaDiCaL 1.9.5 (PySAT) run in conflict-budget chunks so that a wall
clock limit can be enforced (its interrupt does not work from a thread).
Every SAT answer is checked again by lns.is_snake.
"""
import itertools
import os
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lns import N, NV, NB, is_snake, components, order_path  # noqa: E402,F401

POP = [bin(v).count("1") for v in range(NV)]


def subcubes(k):
    """All k-dimensional subcubes as vertex lists."""
    out = []
    for dims in itertools.combinations(range(N), k):
        mask = sum(1 << d for d in dims)
        sub = [sum(((s >> t) & 1) << d for t, d in enumerate(dims)) for s in range(1 << k)]
        for base in range(NV):
            if base & mask:
                continue
            out.append([base | s for s in sub])
    return out


SUB = {}


def get_sub(k):
    if k not in SUB:
        SUB[k] = subcubes(k)
    return SUB[k]


class Model2:
    def __init__(self, kept, target, forbid=(), solver="cadical195",
                 balance=True, hexagons=True, q4=True, q5=False, at_most=None):
        kept = set(kept)
        self.kept = kept
        degK = [0] * NV
        for k in kept:
            for w in NB[k]:
                degK[w] += 1
        bad = set(forbid)
        for k in kept:
            if degK[k] >= 2:
                bad.update(NB[k])
        for v in range(NV):
            if v not in kept and degK[v] >= 3:
                bad.add(v)
        free = [v for v in range(NV) if v not in kept and v not in bad]
        self.free = free
        self.ok = all(degK[k] <= 2 for k in kept)
        self.top = 0
        x = {}
        for v in free:
            x[v] = self.new()
        self.x = x
        cls = []
        ends = []
        for v in free + sorted(kept):
            isfree = v not in kept
            fn = [x[u] for u in NB[v] if u in x]
            c = degK[v]
            guard = [-x[v]] if isfree else []
            cap = 2 - c
            if cap < 0:
                cls.append(guard)
                continue
            if len(fn) > cap:
                for sub in itertools.combinations(fn, cap + 1):
                    cls.append(guard + [-a for a in sub])
            if c == 0:
                cls.append(guard + fn)
            can_end = (c <= 1) and (c == 1 or len(fn) >= 1)
            can_mid = c + len(fn) >= 2
            if not can_end:
                continue
            e = self.new()
            ends.append(e)
            if isfree:
                cls.append([-e, x[v]])
            if c == 1:
                for a in fn:
                    cls.append([-e, -a])
            else:
                for a, b in itertools.combinations(fn, 2):
                    cls.append([-e, -a, -b])
            if not can_mid:
                cls.append(guard + [e])
            elif c == 1:
                cls.append(guard + [e] + fn)
            else:
                for u in fn:
                    cls.append(guard + [e] + [a for a in fn if a != u])
        if len(ends) < 2:
            self.ok = False
        else:
            enc = CardEnc.equals(ends, bound=2, top_id=self.top, encoding=EncType.totalizer)
            cls += enc.clauses
            self.top = max(self.top, enc.nv)
        allowed = kept | set(free)
        self.allowed = allowed
        # square cuts
        for v in allowed:
            for i in range(N):
                for j in range(i + 1, N):
                    a, b, c2 = v ^ (1 << i), v ^ (1 << j), v ^ (1 << i) ^ (1 << j)
                    if v < a and v < b and v < c2 and a in allowed and b in allowed and c2 in allowed:
                        lits = [-x[w] for w in (v, a, b, c2) if w in x]
                        if lits:
                            cls.append(lits)
                        else:
                            self.ok = False
        if hexagons:
            for cube in get_sub(3):
                for p in range(4):
                    hexa = [cube[t] for t in range(8) if t != p and t != 7 - p]
                    if all(w in allowed for w in hexa):
                        lits = [-x[w] for w in hexa if w in x]
                        if lits:
                            cls.append(lits)
                        else:
                            self.ok = False
        for k, capk, on in ((4, 8, q4), (5, 16, q5)):
            if not on:
                continue
            for cube in get_sub(k):
                kc = sum(w in kept for w in cube)
                fl = [x[w] for w in cube if w in x]
                b = capk - kc
                if b < 0:
                    self.ok = False
                elif len(fl) > b:
                    enc = CardEnc.atmost(fl, bound=b, top_id=self.top, encoding=EncType.seqcounter)
                    cls += enc.clauses
                    self.top = max(self.top, enc.nv)
        need = target - len(kept)
        self.need = need
        xs = list(x.values())
        if need > len(free):
            self.ok = False
        if balance and self.ok:
            ev = [x[v] for v in free if POP[v] % 2 == 0]
            od = [x[v] for v in free if POP[v] % 2 == 1]
            ke = sum(1 for v in kept if POP[v] % 2 == 0)
            ko = len(kept) - ke
            E = self.unary(ev, cls)  # E[i] <-> at least i+1 selected
            O = self.unary(od, cls)
            # total colour counts Te = ke + sE, To = ko + sO; |Te - To| <= 1;
            # Te + To >= target  =>  Te, To >= ceil((target - 1) / 2)
            lo = (target - 1 + 1) // 2

            def atleast(U, kc, m):  # clause list forcing kc + s >= m
                r = m - kc
                if r <= 0:
                    return []
                if r > len(U):
                    return [[]]
                return [[U[r - 1]]]

            for cl in atleast(E, ke, lo) + atleast(O, ko, lo):
                if not cl:
                    self.ok = False
                cls.append(cl)
            # Te >= t + 2  ->  To >= t + 1   (and symmetric)
            for (A, ka, B, kb) in ((E, ke, O, ko), (O, ko, E, ke)):
                for i in range(len(A)):
                    ta = ka + i + 1          # A[i] means Ta >= ta
                    need_b = ta - 1          # Tb >= ta - 1
                    r = need_b - kb
                    if r <= 0:
                        continue
                    if r > len(B):
                        cls.append([-A[i]])
                    else:
                        cls.append([-A[i], B[r - 1]])
        if self.ok and need > 0:
            enc = CardEnc.atleast(xs, bound=need, top_id=self.top, encoding=EncType.seqcounter if len(xs) < 300 else EncType.totalizer)
            cls += enc.clauses
            self.top = max(self.top, enc.nv)
        if self.ok and at_most is not None:
            enc = CardEnc.atmost(xs, bound=at_most - len(kept), top_id=self.top, encoding=EncType.seqcounter)
            cls += enc.clauses
            self.top = max(self.top, enc.nv)
        self.nclauses = len(cls)
        self.nvars = self.top
        if any(len(c) == 0 for c in cls):
            self.ok = False
        self.s = Solver(name=solver, bootstrap_with=cls) if self.ok else None
        self.cuts = 0

    def new(self):
        self.top += 1
        return self.top

    def unary(self, lits, cls):
        """Full (two-directional) totalizer; returns U with U[i] <-> sum >= i+1."""
        if not lits:
            return []
        layer = [[l] for l in lits]
        while len(layer) > 1:
            nxt = []
            for t in range(0, len(layer) - 1, 2):
                A, B = layer[t], layer[t + 1]
                C = [self.new() for _ in range(len(A) + len(B))]
                for i in range(len(A) + 1):
                    for j in range(len(B) + 1):
                        if i + j >= 1:
                            # A>=i and B>=j -> C>=i+j
                            cl = [C[i + j - 1]]
                            if i:
                                cl.append(-A[i - 1])
                            if j:
                                cl.append(-B[j - 1])
                            cls.append(cl)
                        if i + j < len(C):
                            # A<=i and B<=j (i.e. not A>=i+1, not B>=j+1) -> not C>=i+j+1
                            cl = [-C[i + j]]
                            if i < len(A):
                                cl.append(A[i])
                            if j < len(B):
                                cl.append(B[j])
                            cls.append(cl)
                nxt.append(C)
            if len(layer) % 2:
                nxt.append(layer[-1])
            layer = nxt
        return layer[0]

    def add(self, cl):
        self.s.add_clause(cl)

    def run(self, time_budget=60.0, chunk=20000, max_rounds=100000):
        if not self.ok:
            return "UNSAT", None
        t0 = time.time()
        for _ in range(max_rounds):
            r = None
            while time.time() - t0 < time_budget:
                self.s.conf_budget(chunk)
                r = self.s.solve_limited()
                if r is not None:
                    break
            if r is None:
                return "UNKNOWN", None
            if not r:
                return "UNSAT", None
            m = self.s.get_model()
            sel = set(self.kept) | {v for v, var in self.x.items() if m[var - 1] > 0}
            comps = components(sel)
            path = None
            for comp in comps:
                p = order_path(comp)
                if p is not None:
                    path = p
                else:
                    cut = [-self.x[v] for v in comp if v in self.x]
                    assert cut, "cycle entirely in kept set"
                    self.s.add_clause(cut)
                    self.cuts += 1
            if len(comps) == 1 and path is not None:
                assert is_snake(path)
                return "SAT", path
        return "UNKNOWN", None

    def close(self):
        if self.s:
            self.s.delete()
