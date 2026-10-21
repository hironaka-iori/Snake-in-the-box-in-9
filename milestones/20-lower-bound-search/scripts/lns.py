"""Large-neighbourhood SAT repair of Q9 snakes.

Given a snake P (vertex list) and a set of released path positions R, every
vertex of P outside R is kept (selected), every vertex that would conflict
with the kept part is excluded, and a SAT model chooses the remaining
selected vertices.  The model asks for an induced subgraph in which every
selected vertex has selected degree 1 or 2, exactly two vertices have degree
1, and at least `target` vertices are selected.  Such a graph is one path
plus disjoint cycles; cycle components are removed lazily by the valid cut
"not every vertex of this cycle is selected" (an induced path contains no
cycle).  A returned graph is accepted only after an independent check.
"""
import itertools
import threading
import time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

N = 9
NV = 1 << N
NB = [[v ^ (1 << k) for k in range(N)] for v in range(NV)]


def is_snake(seq):
    """Independent check: distinct, consecutive adjacent, others at distance >= 2."""
    if len(set(seq)) != len(seq):
        return False
    if any(not (0 <= v < NV) for v in seq):
        return False
    for i in range(len(seq)):
        for j in range(i + 1, len(seq)):
            d = bin(seq[i] ^ seq[j]).count("1")
            if j == i + 1:
                if d != 1:
                    return False
            elif d < 2:
                return False
    return True


def components(sel):
    sel = set(sel)
    seen = set()
    comps = []
    for v in sel:
        if v in seen:
            continue
        stack = [v]
        seen.add(v)
        comp = []
        while stack:
            u = stack.pop()
            comp.append(u)
            for w in NB[u]:
                if w in sel and w not in seen:
                    seen.add(w)
                    stack.append(w)
        comps.append(comp)
    return comps


def order_path(comp):
    cs = set(comp)
    deg = {v: sum(w in cs for w in NB[v]) for v in comp}
    ends = [v for v in comp if deg[v] == 1]
    if len(ends) != 2:
        return None
    seq = [ends[0]]
    prev = None
    while True:
        cur = seq[-1]
        nxt = [w for w in NB[cur] if w in cs and w != prev]
        if not nxt:
            break
        prev = cur
        seq.append(nxt[0])
    return seq if len(seq) == len(comp) else None


class Model:
    def __init__(self, kept, target, forbid=(), solver="glucose42"):
        kept = set(kept)
        self.kept = kept
        degK = {v: sum(w in kept for w in NB[v]) for v in range(NV)}
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
        top = [0]

        def new():
            top[0] += 1
            return top[0]

        x = {v: new() for v in free}
        self.x = x
        cls = []
        ends = []
        # vertices whose degree constraint involves free variables or which may be endpoints
        for v in list(free) + [k for k in kept]:
            isfree = v not in kept
            fn = [x[u] for u in NB[v] if u in x]
            c = degK[v]
            guard = [-x[v]] if isfree else []
            # at most 2
            cap = 2 - c
            if cap < 0:
                cls.append(guard)  # impossible when selected
                continue
            if len(fn) > cap:
                for sub in itertools.combinations(fn, cap + 1):
                    cls.append(guard + [-a for a in sub])
            # at least 1
            if c == 0:
                cls.append(guard + fn)
            # endpoint indicator
            can_end = (c <= 1) and (c == 1 or len(fn) >= 1)
            can_mid = c + len(fn) >= 2
            if not can_end:
                continue  # degree is 2 when selected (enforced by >=2 below)
            e = new()
            ends.append(e)
            if isfree:
                cls.append([-e, x[v]])
            # e -> at most (1-c) free neighbours
            if c == 1:
                for a in fn:
                    cls.append([-e, -a])
            else:
                for a, b in itertools.combinations(fn, 2):
                    cls.append([-e, -a, -b])
            # selected and not e -> at least (2-c) neighbours
            if not can_mid:
                cls.append(guard + [e])
            elif c == 1:
                cls.append(guard + [e] + fn)
            else:
                for u in fn:
                    cls.append(guard + [e] + [a for a in fn if a != u])
        # at least two -- vertices that can only be interior must have degree 2:
        for v in list(free) + list(kept):
            pass
        enc = CardEnc.equals(ends, bound=2, top_id=top[0], encoding=EncType.totalizer)
        cls += enc.clauses
        top[0] = max(top[0], enc.nv)
        need = target - len(kept)
        self.need = need
        if need > len(free):
            self.ok = False
        elif need > 0:
            enc = CardEnc.atleast(list(x.values()), bound=need, top_id=top[0],
                                  encoding=EncType.seqcounter if len(x) < 400 else EncType.totalizer)
            cls += enc.clauses
            top[0] = max(top[0], enc.nv)
        # square cuts
        allowed = kept | set(free)
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
        self.top = top[0]
        self.nclauses = len(cls)
        self.s = Solver(name=solver, bootstrap_with=cls) if self.ok else None
        self.cuts = 0

    def run(self, conf_budget=None, time_budget=None, max_rounds=10000):
        """Returns ('SAT', path) / ('UNSAT', None) / ('UNKNOWN', None)."""
        if not self.ok:
            return "UNSAT", None
        t0 = time.time()
        for _ in range(max_rounds):
            if time_budget is not None and time.time() - t0 > time_budget:
                return "UNKNOWN", None
            if time_budget is not None:
                left = time_budget - (time.time() - t0)
                timer = threading.Timer(max(left, 0.01), self.s.interrupt)
                timer.start()
                r = self.s.solve_limited(expect_interrupt=True)
                timer.cancel()
                self.s.clear_interrupt()
            elif conf_budget is not None:
                self.s.conf_budget(conf_budget)
                r = self.s.solve_limited()
            else:
                r = self.s.solve()
            if r is None:
                return "UNKNOWN", None
            if not r:
                return "UNSAT", None
            m = set(l for l in self.s.get_model() if l > 0)
            sel = set(self.kept) | {v for v, var in self.x.items() if var in m}
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
                return "SAT", path
        return "UNKNOWN", None

    def close(self):
        if self.s:
            self.s.delete()
