"""SAT for "locally forest-like" sets: induced subgraphs of Q_n with maximum degree <= 2, at most
c path components, and no cycle inside any k-subcube (cycles spanning more than k directions are
allowed).  Every induced linear forest is such a set, so UNSAT here is an upper bound for g_n(c).

usage: python3 fakesat.py n c L k [timeout]
Encoding: milestone 29's gforest.encode without its symmetry breaking (that one assumes the
longest component is a path), plus the symmetry breaking below, and lazy cuts that forbid the
vertex set of every found cycle spanning <= k directions (the induced 8-cycles of
4-subcubes are added up front).

Symmetry breaking (valid when L > 4c, so that some component has >= 5 vertices: path components
number at most c, and a cycle spanning >= 5 directions has >= 10 vertices): any 5 consecutive
vertices of a component of size >= 5 form an induced path; map them by an automorphism to
0, e0, e0+e1, e0+e1+e2 and then e1+e2 or e0+e1+e2+e3.
"""
import sys, os, time, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '29-q8-layering', 'scripts'))
import gforest
from gforest import encode, components
from pysat.solvers import Solver


def short_cycles(sel, n, k):
    comps, adj = components(sel, n)
    out = []
    for c in comps:
        if all(len(adj[a]) == 2 for a in c):
            span = 0
            for a in c:
                span |= a ^ c[0]
            if bin(span).count('1') <= k:
                out.append(c)
    return out


def q4_cycles(n):
    """vertex sets of the induced 8-cycles of every 4-subcube of Q_n (168 per 4-subcube)."""
    from itertools import combinations
    base = set()

    def dfs(path):
        u = path[-1]
        for i in range(4):
            w = u ^ (1 << i)
            if w == path[0] and len(path) == 8:
                S = frozenset(path)
                if all(sum((x ^ (1 << j)) in S for j in range(4)) == 2 for x in S):
                    base.add(S)
            elif w not in path and len(path) < 8 and w > path[0]:
                dfs(path + [w])
    for s0 in range(16):
        dfs([s0])
    out = []
    for dirs in combinations(range(n), 4):
        m = sum(1 << d for d in dirs)
        for b in range(1 << n):
            if b & m:
                continue
            for S in base:
                vs = []
                for x in S:
                    v = b
                    for i, d in enumerate(dirs):
                        if x >> i & 1:
                            v |= 1 << d
                    vs.append(v)
                out.append(vs)
    return out


def run(n, c, L, k, tmax=3600, verbose=True):
    assert L > 4 * c
    pool, s, cl = encode(n, c, L, sym=False)
    if k >= 4:
        cl += [[-s[u] for u in cy] for cy in q4_cycles(n)]
    e = [1 << i for i in range(n)]
    v3 = e[0] | e[1] | e[2]
    cl += [[s[0]], [s[e[0]]], [s[e[0] | e[1]]], [s[v3]], [s[e[1] | e[2]], s[v3 | e[3]]]]
    V = 1 << n
    t0 = time.time()
    rounds = 0
    with Solver(name='cadical195', bootstrap_with=cl) as sol:
        while True:
            if time.time() - t0 > tmax:
                return 'UNKNOWN', None, rounds, time.time() - t0
            if not sol.solve():
                return 'UNSAT', None, rounds, time.time() - t0
            mdl = sol.get_model()
            sel = [u for u in range(V) if mdl[s[u] - 1] > 0]
            cyc = short_cycles(sel, n, k)
            if not cyc:
                return 'SAT', sel, rounds, time.time() - t0
            for cy in cyc:
                sol.add_clause([-s[u] for u in cy])
            rounds += 1
            if verbose and rounds % 100 == 0:
                print('  rounds', rounds, '%.0fs' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    n, c, L, k = map(int, sys.argv[1:5])
    tmax = float(sys.argv[5]) if len(sys.argv) > 5 else 3600
    st, sel, r, t = run(n, c, L, k, tmax)
    print(json.dumps(dict(n=n, c=c, L=L, k=k, status=st, rounds=r, time=round(t, 1), witness=sel)), flush=True)
