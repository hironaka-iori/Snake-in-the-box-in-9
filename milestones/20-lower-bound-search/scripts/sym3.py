"""Round 3: SAT search for reversal-symmetric snakes in Q_n.

If a snake P (an induced path with at least n edges using all n directions)
is mapped onto itself as a set by a cube automorphism g, then g acts on P as
a path automorphism, i.e. as the identity or as the reversal.  P spans the
cube affinely, so g = id or g reverses P, and then g^2 = id.  Hence the only
nontrivial symmetry a snake can have is an involution g reversing it, and
order-4 automorphisms are impossible.

Involutions x -> pi(x) ^ c (pi an involution of the coordinates with k
transpositions, pi(c) = c) are, up to conjugation, given by (k, w): c is
zero on the transposed pairs and has weight w on the fixed coordinates.
A reversed path with an odd number of vertices fixes its middle vertex,
so w = 0.  With an even number of vertices g swaps the two ends of the
middle edge, so g(v) = v ^ e_f for some v, which forces w = 1.  Classes with
w >= 2 admit no symmetric snake, and (k, w) = (0, 1) is a translation, which
would make the two path ends adjacent.

Model: one Boolean per g-orbit, lifted to all vertices.  Every selected
vertex has selected degree 1 or 2; exactly one orbit of endpoints (two
endpoints); no coordinate square or hexagon; at most 8 vertices of every
Q4; exactly the requested number of vertices; exactly one fixed vertex
(w = 0) or exactly one selected orbit {v, g(v)} that is an edge (w = 1);
cycle components are removed lazily (no induced path contains a cycle).
Symmetry breaking by the centralizer of g: the middle vertex is 0
(w = 0) or the middle edge is {0, e_f} (w = 1); for w = 0 the path leaves
0 through coordinate 0 of the first pair.
"""
import itertools
import os
import sys
import time

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def is_snake(seq, n):
    """Independent check: distinct, consecutive adjacent, others at distance >= 2."""
    nv = 1 << n
    if len(set(seq)) != len(seq) or any(not (0 <= v < nv) for v in seq):
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


def make_g(n, k, w):
    """pi = (0 1)(2 3)...(2k-2 2k-1); c = bits 2k .. 2k+w-1."""
    pi = list(range(n))
    for t in range(k):
        pi[2 * t], pi[2 * t + 1] = 2 * t + 1, 2 * t
    c = sum(1 << (2 * k + t) for t in range(w))

    def g(x):
        y = 0
        for i in range(n):
            if (x >> i) & 1:
                y |= 1 << pi[i]
        return y ^ c
    return g, pi, c


def subcubes(n, k):
    out = []
    for dims in itertools.combinations(range(n), k):
        mask = sum(1 << d for d in dims)
        sub = [sum(((s >> t) & 1) << d for t, d in enumerate(dims)) for s in range(1 << k)]
        for base in range(1 << n):
            if not base & mask:
                out.append([base | s for s in sub])
    return out


def components(sel, n):
    sel = set(sel)
    seen, comps = set(), []
    for v in sel:
        if v in seen:
            continue
        stack, comp = [v], []
        seen.add(v)
        while stack:
            u = stack.pop()
            comp.append(u)
            for i in range(n):
                w_ = u ^ (1 << i)
                if w_ in sel and w_ not in seen:
                    seen.add(w_)
                    stack.append(w_)
        comps.append(comp)
    return comps


def order_path(comp, n):
    cs = set(comp)
    deg = {v: sum((v ^ (1 << i)) in cs for i in range(n)) for v in comp}
    ends = [v for v in comp if deg[v] == 1]
    if len(comp) == 1:
        return list(comp)
    if len(ends) != 2 or any(d > 2 for d in deg.values()):
        return None
    path, prev, cur = [ends[0]], None, ends[0]
    while True:
        nxt = [cur ^ (1 << i) for i in range(n) if (cur ^ (1 << i)) in cs and (cur ^ (1 << i)) != prev]
        if not nxt:
            break
        prev, cur = cur, nxt[0]
        path.append(cur)
    return path if len(path) == len(comp) else None


class SymModel:
    def __init__(self, n, k, w, nverts, solver="cadical195", q4=True, hexagons=True,
                 forbid_cuts=()):
        assert w in (0, 1) and nverts % 2 == (1 if w == 0 else 0)
        self.n, self.k, self.w, self.nverts = n, k, w, nverts
        nv = 1 << n
        g, pi, c = make_g(n, k, w)
        self.g = g
        self.top = 0
        orb = {}
        self.orbits = []
        for v in range(nv):
            if v in orb:
                continue
            o = sorted({v, g(v)})
            var = self.new()
            for u in o:
                orb[u] = var
            self.orbits.append((var, o))
        self.orb = orb
        cls = []
        ends = []
        for var, o in self.orbits:
            v = o[0]
            nb = {}
            for i in range(n):
                u = v ^ (1 << i)
                nb[orb[u]] = nb.get(orb[u], 0) + 1
            if var in nb:          # v adjacent to g(v): the orbit itself counts
                pass
            items = list(nb.items())
            vs = [a for a, _ in items]
            # degree <= 2: forbid minimal sets with multiplicity >= 3
            for r in (1, 2, 3):
                for sub in itertools.combinations(items, r):
                    m = sum(b for _, b in sub)
                    if m >= 3 and all(m - b < 3 for _, b in sub):
                        cls.append([-var] + [-a for a, _ in sub])
            cls.append([-var] + vs)  # degree >= 1
            if len(o) == 1:
                # fixed vertex: never an endpoint, so degree >= 2
                for a, b in items:
                    if b == 1:
                        cls.append([-var] + [x for x in vs if x != a])
                continue
            e = self.new()
            ends.append(e)
            cls.append([-e, var])
            for a, b in items:
                if b >= 2:
                    cls.append([-e, -a])
            for (a, b), (a2, b2) in itertools.combinations(items, 2):
                cls.append([-e, -a, -a2])
            for a, b in items:
                if b == 1:
                    cls.append([-var, e] + [x for x in vs if x != a])
        enc = CardEnc.equals(ends, bound=1, top_id=self.top, encoding=EncType.seqcounter)
        cls += enc.clauses
        self.top = max(self.top, enc.nv)
        # squares and hexagons (clause over distinct orbit variables)
        seen = set()
        for cube in subcubes(n, 2):
            key = frozenset(orb[u] for u in cube)
            if key not in seen:
                seen.add(key)
                cls.append([-a for a in key])
        if hexagons:
            for cube in subcubes(n, 3):
                for p in range(4):
                    key = frozenset(orb[cube[t]] for t in range(8) if t != p and t != 7 - p)
                    if key not in seen:
                        seen.add(key)
                        cls.append([-a for a in key])
        if q4:
            seenq = set()
            for cube in subcubes(n, 4):
                lits = sorted(orb[u] for u in cube)
                key = tuple(lits)
                if key in seenq:
                    continue
                seenq.add(key)
                enc = CardEnc.atmost(lits, bound=8, top_id=self.top, encoding=EncType.seqcounter)
                cls += enc.clauses
                self.top = max(self.top, enc.nv)
        # special orbits
        fixed = [var for var, o in self.orbits if len(o) == 1]
        edgeorb = [var for var, o in self.orbits if len(o) == 2 and bin(o[0] ^ o[1]).count("1") == 1]
        if w == 0:
            assert fixed and not edgeorb
            cls.append([orb[0]])
            for f in fixed:
                if f != orb[0]:
                    cls.append([-f])
            if k >= 1:
                cls.append([orb[1]])  # path leaves 0 along coordinate 0 (and 1)
        else:
            assert not fixed and edgeorb
            cls.append([orb[0]])
            for f in edgeorb:
                if f != orb[0]:
                    cls.append([-f])
        # exact vertex count: sum over orbits of |orbit| * x
        lits = []
        for var, o in self.orbits:
            lits += [var] * len(o)
        enc = CardEnc.equals(lits, bound=nverts, top_id=self.top, encoding=EncType.totalizer)
        cls += enc.clauses
        self.top = max(self.top, enc.nv)
        for cut in forbid_cuts:
            cls.append(list(cut))
        self.nclauses = len(cls)
        self.s = Solver(name=solver, bootstrap_with=cls)
        self.cuts = 0
        self.cutlist = []

    def new(self):
        self.top += 1
        return self.top

    def run(self, time_budget=60.0, chunk=20000, assumptions=()):
        t0 = time.time()
        assumptions = list(assumptions)
        while True:
            r = None
            while time.time() - t0 < time_budget:
                self.s.conf_budget(chunk)
                r = self.s.solve_limited(assumptions=assumptions)
                if r is not None:
                    break
            if r is None:
                return "UNKNOWN", None
            if not r:
                return "UNSAT", None
            m = self.s.get_model()
            sel = [v for v in range(1 << self.n) if m[self.orb[v] - 1] > 0]
            comps = components(sel, self.n)
            path = None
            for comp in comps:
                p = order_path(comp, self.n)
                if p is not None and len(comps) == 1:
                    path = p
                elif p is None:
                    cut = sorted({-self.orb[v] for v in comp})
                    self.s.add_clause(cut)
                    self.cutlist.append(cut)
                    self.cuts += 1
            if path is not None:
                assert is_snake(path, self.n)
                assert len(path) == self.nverts
                assert sorted(self.g(v) for v in path) == sorted(path)
                return "SAT", path
            if len(comps) > 1 and all(order_path(cp, self.n) is not None for cp in comps):
                raise RuntimeError("several path components despite one endpoint orbit")

    def close(self):
        self.s.delete()


if __name__ == "__main__":
    import argparse
    import json
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=9)
    ap.add_argument("--k", type=int, required=True)
    ap.add_argument("--edges", type=int, required=True)
    ap.add_argument("--tl", type=float, default=60)
    ap.add_argument("--noq4", action="store_true")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    nverts = a.edges + 1
    w = 0 if nverts % 2 else 1
    t0 = time.time()
    M = SymModel(a.n, a.k, w, nverts, q4=not a.noq4)
    tb = time.time() - t0
    st, p = M.run(a.tl)
    rec = dict(n=a.n, k=a.k, w=w, edges=a.edges, status=st, build=round(tb, 1),
               time=round(time.time() - t0, 1), cuts=M.cuts, clauses=M.nclauses)
    print(json.dumps(rec), flush=True)
    if p and a.out:
        json.dump({"vertex_sequence": p, **rec}, open(a.out, "w"))
