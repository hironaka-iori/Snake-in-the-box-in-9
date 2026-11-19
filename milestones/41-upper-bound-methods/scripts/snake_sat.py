"""Global SAT model of 'an induced path with >= V vertices in Q_n', with lazy cycle cuts.
Clauses: max degree 2 for selected vertices, no isolated selected vertex, at most two selected
vertices of degree one, at least V selected, vertex 0, e0, e1 selected (symmetry: an internal
vertex and its path neighbours).  Every model is then one path plus induced cycles; for each
cycle C found we add the clause 'not all of C' (valid for every snake) and resolve.
Every added clause is implied by the snake definition, so UNSAT is a refutation (a DRAT/LRAT
proof of the final CNF would certify it).  usage: python3 snake_sat.py n V [seconds]
"""
import sys, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def totalizer(xs, pool, cls):
    """Full (two-way) unary totalizer: returns r with r[j-1] <-> (sum xs >= j)."""
    if len(xs) == 1: return list(xs)
    h = len(xs) // 2
    a = totalizer(xs[:h], pool, cls); b = totalizer(xs[h:], pool, cls)
    p, q = len(a), len(b)
    r = [pool.id() for _ in range(p + q)]
    A = lambda i: True if i == 0 else (False if i > p else a[i - 1])
    B = lambda j: True if j == 0 else (False if j > q else b[j - 1])
    def lit(x): return x
    for i in range(p + 1):
        for j in range(q + 1):
            if i + j >= 1:
                c = [r[i + j - 1]]
                if i: c.append(-a[i - 1])
                if j: c.append(-b[j - 1])
                cls.append(c)
            if i + j + 1 <= p + q:
                c = [-r[i + j]]
                if i + 1 <= p: c.append(a[i])
                if j + 1 <= q: c.append(b[j])
                cls.append(c)
    return r

def subcubes(n, k):
    from itertools import combinations
    for D in combinations(range(n), k):
        free = sum(1 << i for i in D)
        for base in range(1 << n):
            if base & free: continue
            vs = [base]
            for i in D:
                vs = vs + [x | (1 << i) for x in vs]
            yield vs

def build(n, V, opts=()):
    N = 1 << n
    pool = IDPool()
    s = [pool.id(("s", u)) for u in range(N)]
    cls = []
    d1 = []
    for u in range(N):
        nb = [s[u ^ (1 << i)] for i in range(n)]
        # selected -> at most 2 selected neighbours
        am2 = CardEnc.atmost(nb, bound=2, vpool=pool, encoding=EncType.seqcounter)
        g = s[u]
        for c in am2.clauses: cls.append(c + [-g])
        cls.append([-g] + nb)              # selected -> at least one selected neighbour
        # t_u <- selected and at most one selected neighbour (degree-1 indicator, one direction suffices)
        t = pool.id(("t", u)); d1.append(t)
        # if selected and no two selected neighbours then t: for every pair? use: s_u and (sum nb <= 1) -> t
        # encode: s_u and not (exists pair i<j with both) -> t ; via auxiliary p_u = 'deg >= 2'
        p = pool.id(("p", u))
        # p -> at least two neighbours: p -> OR over pairs; use ladder: p -> for each i: (nb_i -> OR others) and p -> OR nb
        cls.append([-p] + nb)
        for i in range(n):
            cls.append([-p, -nb[i]] + [nb[j] for j in range(n) if j != i])
        cls.append([-g, p, t])
    am = CardEnc.atmost(d1, bound=2, vpool=pool, encoding=EncType.seqcounter)
    cls += am.clauses
    al = CardEnc.atleast(s, bound=V, vpool=pool, encoding=EncType.seqcounter)
    cls += al.clauses
    cls += [[s[0]], [s[1]], [s[2]]]
    for k, cap in ((4, 8), (5, 16), (6, 32), (7, 64)):
        if f"cap{k}" in opts and k < n:
            for vs in subcubes(n, k):
                cls += CardEnc.atmost([s[u] for u in vs], bound=cap, vpool=pool, encoding=EncType.seqcounter).clauses
    if "sort" in opts:
        r = []
        for i in range(n):
            es = []
            for u in range(N):
                w = u ^ (1 << i)
                if u < w:
                    e = pool.id(("e", u, w)); es.append(e)
                    cls += [[-e, s[u]], [-e, s[w]], [e, -s[u], -s[w]]]
            r.append(totalizer(es, pool, cls))
        pairs = [(0, 1)] + [(i, i + 1) for i in range(2, n - 1)]
        for i, j in pairs:
            for t in range(len(r[j])):
                cls.append([-r[j][t], r[i][t]])
    return cls, s

def cycles(n, S):
    S = set(S); seen = set(); out = []
    for u in S:
        if u in seen: continue
        comp = [u]; seen.add(u); st = [u]
        while st:
            x = st.pop()
            for i in range(n):
                w = x ^ (1 << i)
                if w in S and w not in seen: seen.add(w); comp.append(w); st.append(w)
        if all(sum((x ^ (1 << i)) in S for i in range(n)) == 2 for x in comp):
            out.append(comp)
    return out

if __name__ == "__main__":
    n, V = int(sys.argv[1]), int(sys.argv[2])
    lim = float(sys.argv[3]) if len(sys.argv) > 3 else 1e9
    opts = sys.argv[4].split(",") if len(sys.argv) > 4 else []
    cls, s = build(n, V, opts)
    t0 = time.time(); cuts = 0
    with Solver(name="cadical153", bootstrap_with=cls) as sol:
        while True:
            if time.time() - t0 > lim: print(f"n={n} V={V} opts={opts} status=TIMEOUT cuts={cuts}"); break
            if not sol.solve():
                print(f"n={n} V={V} opts={opts} status=UNSAT cuts={cuts} wall={time.time()-t0:.1f}", flush=True); break
            mod = set(l for l in sol.get_model() if l > 0)
            S = [u for u in range(1 << n) if s[u] in mod]
            cyc = cycles(n, S)
            if not cyc:
                print(f"n={n} V={V} opts={opts} status=SAT v={len(S)} cuts={cuts} wall={time.time()-t0:.1f}", flush=True); break
            for C in cyc:
                sol.add_clause([-s[u] for u in C]); cuts += 1
