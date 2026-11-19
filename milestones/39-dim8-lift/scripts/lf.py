"""Induced linear forests in Q_n with at most c paths and exactly L vertices (SAT, lazy cycle cuts).

Why |F| = L exactly is WLOG for "is there a forest with >= L vertices and <= c paths": deleting
an end vertex of a path never increases the number of paths.

Encoding
  s_u            vertex selected
  deg <= 2       direct clauses: no selected vertex with 3 selected neighbours
  squares, induced 6-cycles of Q3 (and optionally induced 8-cycles of Q4) forbidden up front
  y_uw <-> s_u & s_w for every edge;  sum y >= L - c   (a forest on L vertices with p paths has L-p edges)
  longer cycles: lazy cuts (each cut forbids selecting all vertices of one found cycle)
  optional fixed block: the vertices of the copy (x_hi = 0) of Q_k (low k coordinates) are fixed to a
  given set A, and every other copy (x_hi = t) has at most |A| vertices (WLOG when A is a largest copy).
"""
import sys, time, json, itertools
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def induced_cycles_q4():
    """All induced 8-cycles of Q4 as vertex sets (by brute force)."""
    V = 16
    adj = [[u ^ (1 << i) for i in range(4)] for u in range(V)]
    out = set()
    def dfs(path, used):
        u = path[-1]
        for w in adj[u]:
            if w == path[0] and len(path) >= 4:
                S = frozenset(path)
                # induced: each vertex has exactly 2 neighbours in S
                if all(sum(1 for x in adj[v] if x in S) == 2 for v in S):
                    out.add(S)
            if w in used or w < path[0]:
                continue
            used.add(w); path.append(w)
            dfs(path, used)
            path.pop(); used.discard(w)
    for s in range(V):
        dfs([s], {s})
    return [sorted(S) for S in out]


def subcube_cycles(n, with8=False):
    out = []
    V = 1 << n
    for a, b in combinations(range(n), 2):
        m = (1 << a) | (1 << b)
        for u in range(V):
            if u & m == 0:
                out.append([u, u | 1 << a, u | m, u | 1 << b])
    for dirs in combinations(range(n), 3):
        m = sum(1 << d for d in dirs)
        for u in range(V):
            if u & m == 0:
                cube = [u | x for x in range(V) if x & ~m == 0]
                for x in cube:
                    if x < x ^ m:
                        out.append([y for y in cube if y != x and y != x ^ m])
    if with8:
        c8 = induced_cycles_q4()
        c8 = [S for S in c8 if len(S) == 8]
        for dirs in combinations(range(n), 4):
            m = sum(1 << d for d in dirs)
            emb = lambda x: sum(1 << dirs[i] for i in range(4) if x >> i & 1)
            for u in range(V):
                if u & m == 0:
                    for S in c8:
                        out.append([u | emb(x) for x in S])
    return out


def find_cycles(sel, n):
    S = set(sel); seen = set(); cyc = []
    for u in sel:
        if u in seen:
            continue
        comp = []; st = [u]; seen.add(u)
        while st:
            x = st.pop(); comp.append(x)
            for i in range(n):
                y = x ^ (1 << i)
                if y in S and y not in seen:
                    seen.add(y); st.append(y)
        degs = [sum(1 for i in range(n) if x ^ (1 << i) in S) for x in comp]
        if all(d == 2 for d in degs):
            cyc.append(comp)
    return cyc


def check_forest(sel, n):
    S = set(sel)
    for x in S:
        if sum(1 for i in range(n) if x ^ (1 << i) in S) > 2:
            return None
    if find_cycles(sel, n):
        return None
    E = sum(1 for x in S for i in range(n) if x ^ (1 << i) in S) // 2
    return len(S) - E      # number of paths


def encode(n, c, L, fix=None, with8=False, sub4=False, enc=EncType.kmtotalizer):
    V = 1 << n
    pool = IDPool()
    s = [pool.id(('s', u)) for u in range(V)]
    cl = []
    for u in range(V):
        nb = [s[u ^ (1 << i)] for i in range(n)]
        for a, b, d in combinations(nb, 3):
            cl.append([-s[u], -a, -b, -d])
    ys = []
    for u in range(V):
        for i in range(n):
            w = u ^ (1 << i)
            if u < w:
                y = pool.id(('y', u, w)); ys.append(y)
                cl += [[-y, s[u]], [-y, s[w]], [y, -s[u], -s[w]]]
    for cy in subcube_cycles(n, with8):
        cl.append([-s[u] for u in cy])
    top = pool.top
    card = CardEnc.equals(s, bound=L, top_id=pool.top, encoding=enc)
    cl += card.clauses; pool.occupy(pool.top + 1, card.nv); pool.top = max(pool.top, card.nv)
    card = CardEnc.atleast(ys, bound=L - c, top_id=pool.top, encoding=enc)
    cl += card.clauses; pool.top = max(pool.top, card.nv)
    if sub4:
        # every 4-subcube holds at most 8 vertices (g4 = 8)
        for dirs in combinations(range(n), 4):
            m = sum(1 << d for d in dirs)
            for base in range(V):
                if base & m == 0:
                    lits = [s[u] for u in range(V) if u & ~m == base]
                    card = CardEnc.atmost(lits, bound=8, top_id=pool.top, encoding=EncType.seqcounter)
                    cl += card.clauses; pool.top = max(pool.top, card.nv)
    if fix is not None:
        k, A = fix                       # copy 0 of Q_k (low k coords) fixed to set A
        A = set(A)
        for x in range(1 << k):
            cl.append([s[x]] if x in A else [-s[x]])
        for t in range(1, 1 << (n - k)):
            lits = [s[(t << k) | x] for x in range(1 << k)]
            card = CardEnc.atmost(lits, bound=len(A), top_id=pool.top, encoding=EncType.seqcounter)
            cl += card.clauses; pool.top = max(pool.top, card.nv)
    return pool, s, cl


def search(n, c, L, tmax=600, fix=None, with8=False, sub4=False, extra=None, verbose=False, cuts=None,
           solver='cadical195'):
    pool, s, cl = encode(n, c, L, fix=fix, with8=with8, sub4=sub4)
    cuts = cuts if cuts is not None else []
    t0 = time.time(); rounds = 0
    with Solver(name=solver, bootstrap_with=cl + (extra or []) + [[-s[u] for u in cy] for cy in cuts]) as sol:
        while True:
            left = tmax - (time.time() - t0)
            if left <= 0:
                return 'UNKNOWN', None, rounds
            # cadical195 in pysat has no time limit hook; rely on outer timeout of the process
            r = sol.solve()
            rounds += 1
            if not r:
                return 'UNSAT', None, rounds
            m = sol.get_model()
            sel = [u for u in range(1 << n) if m[s[u] - 1] > 0]
            cy = find_cycles(sel, n)
            if not cy:
                return 'SAT', sel, rounds
            for C in cy:
                sol.add_clause([-s[u] for u in C]); cuts.append(C)
            if verbose and rounds % 50 == 0:
                print('  round', rounds, 'cuts', len(cuts), round(time.time() - t0, 1), flush=True)


if __name__ == '__main__':
    n, c, L = map(int, sys.argv[1:4])
    with8 = '--c8' in sys.argv; sub4 = '--sub4' in sys.argv
    t = time.time()
    st, sel, r = search(n, c, L, 10**9, with8=with8, sub4=sub4, verbose=True)
    print(json.dumps(dict(n=n, c=c, L=L, c8=with8, sub4=sub4, status=st, rounds=r, sec=round(time.time() - t, 1),
                          paths=check_forest(sel, n) if sel else None, witness=sel)), flush=True)
