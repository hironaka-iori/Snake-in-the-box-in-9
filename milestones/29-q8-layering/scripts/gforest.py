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
SYMCAP = 99      # cap on the symmetry-breaking depth r (for soundness cross-checks)


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


def encode(n, cmax, L, cmin=None, short=None, sym=True, pool=None, extra=None, levels=None, sub=None):
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
        r = min(-(-L // max(cmax, 1)), SYMCAP)
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
    if levels:
        # acyclicity by levels: o(u,j) = [level(u) >= j], j = 1..D.  Every internal vertex has a
        # selected neighbour of strictly smaller level (so no cycle survives: look at its minimum).
        # Complete when D >= floor((longest path - 1)/2); D = 2^(n-2) always suffices.
        D = levels
        o = {(u, j): pool.id(('o', u, j)) for u in range(V) for j in range(1, D + 1)}
        for u in range(V):
            two = pool.id(('two', u))
            for j in range(1, D):
                cl.append([-o[u, j + 1], o[u, j]])
            cl.append([-two, o[u, 1]])
            for j in range(1, D + 1):
                al = []
                for i in range(n):
                    y = u ^ (1 << i)
                    a = pool.id(('a', u, i, j)); al.append(a)
                    cl += [[-a, s[y]], [-a, -o[y, j]]]
                cl.append([-two] + ([o[u, j + 1]] if j < D else []) + al)
    if sub:
        for k, g in sub:
            cl += subcube_bounds(n, k, g, s, pool)
    if extra:
        cl += extra
    return pool, s, cl


def subcube_bounds(n, k, g, s, pool):
    """Implied constraints |F cap Q| <= g_k(p_Q) for every k-subcube Q, where p_Q is the number of
    pieces (paths of F cap Q), from a table g = {p: upper bound for Q_k} (beyond the table 2^(k-1)).
    2 p_Q = sum over x in F cap Q of (2 - deg_Q(x)), counted by local endpoint literals.
    For each j with g(j) < 2^(k-1):  y_j or (2p_Q >= 2j+1)  and  not y_j or (|F cap Q| <= g(j))."""
    half = 1 << (k - 1)
    V = 1 << n
    out = []
    js = [j for j in sorted(g) if g[j] < half]
    for dirs in combinations(range(n), k):
        m = sum(1 << d for d in dirs)
        for base in range(V):
            if base & m:
                continue
            tag = ('Q', m, base)
            verts = [u for u in range(V) if (u & ~m) == base]
            ends = []
            for u in verts:
                nb = [s[u ^ (1 << d)] for d in dirs]
                pr = []
                for a, b in combinations(range(k), 2):
                    p = pool.id(tag + ('p', u, a, b)); pr.append(p)
                    out.extend([[-p, nb[a]], [-p, nb[b]], [p, -nb[a], -nb[b]]])
                two = pool.id(tag + ('two', u)); anyn = pool.id(tag + ('any', u))
                out.append([-two] + pr); out.extend([[two, -p] for p in pr])
                out.append([-anyn] + nb); out.extend([[anyn, -x] for x in nb])
                e1 = pool.id(tag + ('e1', u)); e0 = pool.id(tag + ('e0', u))
                out.extend([[-e1, s[u]], [-e1, -two], [e1, -s[u], two]])
                out.extend([[-e0, s[u]], [-e0, -anyn], [e0, -s[u], anyn]])
                ends += [e1, e0]
            vs = [s[u] for u in verts]
            for j in js:
                y = pool.id(tag + ('y', j))
                for c in CardEnc.atleast(ends, bound=2 * j + 1, vpool=pool, encoding=EncType.seqcounter).clauses:
                    out.append(c + [y])
                for c in CardEnc.atmost(vs, bound=g[j], vpool=pool, encoding=EncType.seqcounter).clauses:
                    out.append(c + [-y])
            for c in CardEnc.atmost(vs, bound=half, vpool=pool, encoding=EncType.seqcounter).clauses:
                out.append(c)
    return out


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


def search(n, cmax, L, tmax=600, cmin=None, short=None, sym=True, extra=None, verbose=False, levels=None, sub=None):
    pool, s, cl = encode(n, cmax, L, cmin, short, sym, extra=extra, levels=levels, sub=sub)
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
    levels = None
    if '--levels' in args:
        ix = args.index('--levels'); levels = int(args[ix + 1]); del args[ix:ix + 2]
    if '--short' in args:
        ix = args.index('--short'); short = int(args[ix + 1]); del args[ix:ix + 2]
    nums = [a for a in args if not a.startswith('--')]
    n, c, L = map(int, nums[:3])
    tmax = float(nums[3]) if len(nums) > 3 else 600
    st, sel, r = search(n, c, L, tmax, cmin=c if exact else None, short=short, verbose=True, levels=levels)
    print('n=%d paths%s%d |F|>=%d short=%s: %s (cut rounds %d)' % (n, '=' if exact else '<=', c, L, short, st, r), flush=True)
    if sel:
        print(' witness |F|=%d paths, sizes:' % len(sel), check_forest(sel, n))
        print(json.dumps(sel))
