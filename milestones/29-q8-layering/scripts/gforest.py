"""Induced linear forests in Q_n with a bounded number of paths (SAT, CaDiCaL via python-sat).

g_n(c)   = max |F| over induced linear forests F of Q_n with at most c paths,
g=_n(c)  = the same with exactly c paths,
g3_n(c,t)= exactly c paths, at most t of which have fewer than 3 vertices.

An induced linear forest is a vertex set whose induced subgraph has maximum degree 2 and no
cycle.  Encoding: selection s_u, degree <= 2, endpoint indicators (an isolated vertex counts as
two endpoints), cardinalities, all 4-cycles and the induced 6-cycles of 3-subcubes forbidden up
front, longer cycles excluded lazily (a cut forbids selecting all vertices of a found cycle; it is
valid for every forest, so cuts are kept across queries).

Symmetry breaking (valid when the longest path has >= r vertices, r = ceil(L / c)): translate an
endpoint of a longest path to 0 and permute coordinates so that it starts
0, e0, e0+e1, e0+e1+e2, and its fifth vertex is e1+e2 or e0+e1+e2+e3.

usage:  python3 gforest.py n cmax L [timeout] [--exact] [--short t]
"""
import sys, time, json
from itertools import combinations
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver

SOLVER = 'cadical195'


def cube_cycles(n):
    """4-cycles (squares) and induced 6-cycles of 3-subcubes of Q_n."""
    out = []
    V = 1 << n
    for a, b in combinations(range(n), 2):
        m = (1 << a) | (1 << b)
        for u in range(V):
            if u & m == 0:
                out.append([u, u | 1 << a, u | m, u | 1 << b])
    for a, b, c in combinations(range(n), 3):
        m = (1 << a) | (1 << b) | (1 << c)
        for u in range(V):
            if u & m == 0:
                cube = [u | x for x in range(V) if x & ~m == 0]
                for x in cube:            # omit an antipodal pair {x, x^m}
                    if x < x ^ m:
                        out.append([y for y in cube if y != x and y != x ^ m])
    return out


def encode(n, cmax, L, cmin=None, short=None, sym=True, pool=None, extra=None):
    V = 1 << n
    pool = pool or IDPool()
    s = [pool.id(('s', u)) for u in range(V)]
    cl = []
    ends = []
    deg1 = []
    for u in range(V):
        nb = [s[u ^ (1 << i)] for i in range(n)]
        for x in CardEnc.atmost(nb, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
            cl.append(x + [-s[u]])
        # p_ab <-> nb_a & nb_b ; two <-> OR p ; any <-> OR nb
        pr = []
        for a, b in combinations(range(n), 2):
            p = pool.id(('p', u, a, b)); pr.append(p)
            cl += [[-p, nb[a]], [-p, nb[b]], [p, -nb[a], -nb[b]]]
        two = pool.id(('two', u)); anyn = pool.id(('any', u))
        cl.append([-two] + pr); cl += [[two, -p] for p in pr]
        cl.append([-anyn] + nb); cl += [[anyn, -x] for x in nb]
        e1 = pool.id(('e1', u)); e0 = pool.id(('e0', u))
        # e1 <-> s & ~two ; e0 <-> s & ~any
        cl += [[-e1, s[u]], [-e1, -two], [e1, -s[u], two]]
        cl += [[-e0, s[u]], [-e0, -anyn], [e0, -s[u], anyn]]
        ends += [e1, e0]
        d1 = pool.id(('d1', u))        # selected with exactly one selected neighbour
        cl += [[-d1, e1], [-d1, anyn], [d1, -e1, -anyn]]
        deg1.append(d1)
    cl += [x for x in CardEnc.atmost(ends, bound=2 * cmax, vpool=pool, encoding=EncType.seqcounter).clauses]
    if cmin is not None:
        cl += [x for x in CardEnc.atleast(ends, bound=2 * cmin, vpool=pool, encoding=EncType.seqcounter).clauses]
    if short is not None:
        sh = [pool.id(('e0', u)) for u in range(V)]
        for u in range(V):
            for i in range(n):
                w = u ^ (1 << i)
                if u < w:
                    d = pool.id(('K2', u, w))
                    cl += [[-d, deg1[u]], [-d, deg1[w]], [-d, s[w]], [d, -deg1[u], -deg1[w], -s[w]]]
                    sh.append(d)
        cl += [x for x in CardEnc.atmost(sh, bound=short, vpool=pool, encoding=EncType.seqcounter).clauses]
    cl += [x for x in CardEnc.atleast(s, bound=L, vpool=pool, encoding=EncType.seqcounter).clauses]
    for cy in cube_cycles(n):
        cl.append([-s[u] for u in cy])
    if sym:
        r = -(-L // max(cmax, 1))
        e = [1 << i for i in range(n)]
        cl.append([s[0]]); cl.append([-pool.id(('two', 0))])
        if r >= 2:
            cl.append([s[e[0]]]); cl += [[-s[e[i]]] for i in range(1, n)]
        if r >= 3:
            cl.append([s[e[0] | e[1]]])
        if r >= 4 and n >= 3:
            v3 = e[0] | e[1] | e[2]
            cl.append([s[v3]]); cl += [[-s[e[0] | e[1] | e[i]]] for i in range(3, n)]
        if r >= 5 and n >= 4:
            v3 = e[0] | e[1] | e[2]
            cl.append([s[e[1] | e[2]], s[v3 | e[3]]]); cl += [[-s[v3 | e[i]]] for i in range(4, n)]
    if extra:
        cl += extra
    return pool, s, cl


def components(sel, n):
    sel = set(sel)
    adj = {u: [u ^ (1 << i) for i in range(n) if u ^ (1 << i) in sel] for u in sel}
    seen, comps = set(), []
    for u in sel:
        if u in seen:
            continue
        comp, st = [], [u]; seen.add(u)
        while st:
            a = st.pop(); comp.append(a)
            for b in adj[a]:
                if b not in seen:
                    seen.add(b); st.append(b)
        comps.append(comp)
    return comps, adj


def cycles(sel, n):
    comps, adj = components(sel, n)
    return [c for c in comps if all(len(adj[a]) == 2 for a in c)]


def check_forest(sel, n):
    comps, adj = components(sel, n)
    assert all(len(adj[a]) <= 2 for a in sel)
    assert not any(all(len(adj[a]) == 2 for a in c) for c in comps)
    return len(comps), sorted(len(c) for c in comps)


CUTS = {}


def search(n, cmax, L, tmax=600, cmin=None, short=None, sym=True, extra=None, verbose=False):
    pool, s, cl = encode(n, cmax, L, cmin, short, sym, extra=extra)
    cuts = CUTS.setdefault(n, [])
    V = 1 << n
    t0 = time.time(); rounds = 0
    with Solver(name=SOLVER, bootstrap_with=cl + [[-s[u] for u in cy] for cy in cuts]) as sol:
        while True:
            left = tmax - (time.time() - t0)
            if left <= 0:
                return 'UNKNOWN', None, rounds
            if hasattr(sol, 'solve_limited') and SOLVER.startswith('glucose'):
                r = sol.solve()
            else:
                r = sol.solve()
            if not r:
                return 'UNSAT', None, rounds
            mdl = sol.get_model()
            sel = [u for u in range(V) if mdl[s[u] - 1] > 0]
            cyc = cycles(sel, n)
            if not cyc:
                return 'SAT', sel, rounds
            for cy in cyc:
                sol.add_clause([-s[u] for u in cy]); cuts.append(cy)
            rounds += 1
            if verbose and rounds % 50 == 0:
                print('  rounds', rounds, 'time %.0f' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    args = sys.argv[1:]
    exact = '--exact' in args
    short = None
    if '--short' in args:
        short = int(args[args.index('--short') + 1])
    nums = [a for a in args if not a.startswith('--')]
    if short is not None:
        nums.remove(str(short))
    n, c, L = map(int, nums[:3])
    tmax = float(nums[3]) if len(nums) > 3 else 600
    st, sel, r = search(n, c, L, tmax, cmin=c if exact else None, short=short, verbose=True)
    print('n=%d paths%s%d |F|>=%d short=%s: %s (cut rounds %d)' % (n, '=' if exact else '<=', c, L, short, st, r), flush=True)
    if sel:
        print(' witness |F|=%d paths, sizes:' % len(sel), check_forest(sel, n))
        print(json.dumps(sel))
