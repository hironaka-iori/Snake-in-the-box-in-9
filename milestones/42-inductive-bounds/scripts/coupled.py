"""Coupled facet split (SAT, CaDiCaL via python-sat, lazy cycle cuts).

A snake S of Q_N cut along the last coordinate gives A = {x : (x,0) in S}, B = {x : (x,1) in S},
both induced linear forests of Q_n (n = N-1).  Necessary conditions used here:
  * A, B induced linear forests of Q_n;
  * crossing points T = A & B: every x in T has degA(x) <= 1 and degB(x) <= 1;
  * free ends: (#path-ends of A) + (#path-ends of B) - 2|T| <= 2 (isolated vertex = 2 ends);
  * |T| <= K (K = crossings in the cut direction).
mode 'coupled': only the above.  mode 'snake': additionally lazy cuts on cycles of the lifted set
in Q_N, so a model is exactly a snake of Q_N with <= K crossings in the last direction.
Prints the largest |A|+|B| (vertices of the lifted set) found, by increasing targets.

usage: python3 coupled.py n K mode [start] [timeout_per_query]
"""
import sys, time
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def squares(n):
    out = []
    for a, b in combinations(range(n), 2):
        m = (1 << a) | (1 << b)
        for u in range(1 << n):
            if u & m == 0:
                out.append([u, u | 1 << a, u | m, u | 1 << b])
    return out


def forest_part(n, s, pool, cl, tag):
    V = 1 << n
    ends = []
    one = {}
    for u in range(V):
        nb = [s[u ^ (1 << i)] for i in range(n)]
        for x in CardEnc.atmost(nb, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
            cl.append(x + [-s[u]])
        pr = []
        for a, b in combinations(range(n), 2):
            p = pool.id((tag, 'p', u, a, b)); pr.append(p)
            cl += [[-p, nb[a]], [-p, nb[b]], [p, -nb[a], -nb[b]]]
        two = pool.id((tag, 'two', u)); anyn = pool.id((tag, 'any', u))
        cl.append([-two] + pr); cl += [[two, -p] for p in pr]
        cl.append([-anyn] + nb); cl += [[anyn, -x] for x in nb]
        e1 = pool.id((tag, 'e1', u)); e0 = pool.id((tag, 'e0', u))
        cl += [[-e1, s[u]], [-e1, -two], [e1, -s[u], two]]
        cl += [[-e0, s[u]], [-e0, -anyn], [e0, -s[u], anyn]]
        ends += [e1, e0]
        one[u] = two
    for sq in squares(n):
        cl.append([-s[u] for u in sq])
    return ends, one


def build(n, K):
    V = 1 << n
    pool = IDPool()
    a = [pool.id(('a', u)) for u in range(V)]
    b = [pool.id(('b', u)) for u in range(V)]
    cl = []
    endsA, twoA = forest_part(n, a, pool, cl, 'A')
    endsB, twoB = forest_part(n, b, pool, cl, 'B')
    t = []
    nt2 = []
    for u in range(V):
        x = pool.id(('t', u)); t.append(x)
        cl += [[-x, a[u]], [-x, b[u]], [x, -a[u], -b[u]]]
        cl += [[-x, -twoA[u]], [-x, -twoB[u]]]
        for j in range(2):
            y = pool.id(('nt', u, j)); nt2.append(y)
            cl += [[y, x], [-y, -x]]
    # endsA + endsB + 2 * #(not t) <= 2 + 2V
    cl += CardEnc.atmost(endsA + endsB + nt2, bound=2 + 2 * V, vpool=pool, encoding=EncType.seqcounter).clauses
    cl += CardEnc.atmost(t, bound=K, vpool=pool, encoding=EncType.seqcounter).clauses
    # symmetry: translation puts a crossing point (if K >= 1) at 0
    if K >= 1:
        cl.append([t[0]])
    return pool, a, b, cl


def comps_cycles(n, sel, adj):
    """Return vertex lists of cycles (components where every vertex has degree 2)."""
    seen = set(); cyc = []
    for u in sel:
        if u in seen:
            continue
        comp = []; st = [u]; seen.add(u)
        while st:
            x = st.pop(); comp.append(x)
            for y in adj(x):
                if y in sel and y not in seen:
                    seen.add(y); st.append(y)
        if all(sum(1 for y in adj(x) if y in sel) == 2 for x in comp):
            cyc.append(comp)
    return cyc


def main():
    n, K, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    start = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    V = 1 << n
    pool, a, b, cl = build(n, K)
    best = None
    L = start
    cuts = []
    while True:
        card = CardEnc.atleast(a + b, bound=L, vpool=pool, encoding=EncType.seqcounter).clauses
        t0 = time.time(); rounds = 0
        with Solver(name='cadical195', bootstrap_with=cl + card + cuts) as S:
            while True:
                if not S.solve():
                    res = 'UNSAT'; break
                m = set(x for x in S.get_model() if x > 0)
                A = set(u for u in range(V) if a[u] in m); B = set(u for u in range(V) if b[u] in m)
                new = []
                adjq = lambda x: [x ^ (1 << i) for i in range(n)]
                for X, var in ((A, a), (B, b)):
                    for c in comps_cycles(n, X, adjq):
                        new.append([-var[u] for u in c])
                if mode == 'snake' and not new:
                    lift = set(A) | set(u | V for u in B)
                    adjl = lambda x: [x ^ (1 << i) for i in range(n + 1)]
                    for c in comps_cycles(n + 1, lift, adjl):
                        new.append([-(a[u] if u < V else b[u ^ V]) for u in c])
                if not new:
                    res = 'SAT'; break
                rounds += 1
                for c in new:
                    S.add_clause(c); cuts.append(c)
        print(f"n={n} K={K} mode={mode} L={L} {res} {time.time()-t0:.1f}s cuts={rounds}"
              + (f" |A|={len(A)} |B|={len(B)} |T|={len(A & B)}" if res == 'SAT' else ''), flush=True)
        if res == 'UNSAT':
            print(f"RESULT n={n} K={K} mode={mode} max={L-1}", flush=True)
            break
        best = len(A) + len(B)
        L = best + 1


if __name__ == '__main__':
    main()
