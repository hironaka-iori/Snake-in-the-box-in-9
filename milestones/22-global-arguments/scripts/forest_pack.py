"""Large induced linear forests with few components in Q_m (SAT, lazy cycle cuts).

g_m(c) = max |F| over induced linear forests F of Q_m with at most c paths.
Layer argument: for a snake in Q_{m+1} with n_i edges in direction i, the two
halves are induced linear forests of Q_m with c0 + c1 = n_i + 1 paths and
|c0 - c1| <= 1, so v <= g_m(floor((n_i+1)/2)) + g_m(ceil((n_i+1)/2)).
usage: python3 forest_pack.py m c L [timeout_s]  -> SAT witness or UNSAT/UNKNOWN
"""
import sys, time, json
from itertools import combinations
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def search(m, c, L, tmax=600):
    V = 1 << m
    pool = IDPool()
    s = [pool.id(('s', u)) for u in range(V)]
    cnf = CNF()
    ends = []
    for u in range(V):
        nb = [s[u ^ (1 << i)] for i in range(m)]
        for cl in CardEnc.atmost(nb, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses:
            cnf.append(cl + [-s[u]])
        # e1: s_u and at most one neighbour  -> counts as an endpoint (weight 1)
        # e0: s_u and no neighbour           -> isolated (extra weight 1)
        e1 = pool.id(('e1', u)); e0 = pool.id(('e0', u))
        pairs = []
        for a, b in combinations(range(m), 2):
            p = pool.id(('p', u, a, b)); pairs.append(p)
            cnf.append([-p, nb[a]]); cnf.append([-p, nb[b]])
        cnf.append([-s[u], e1] + pairs)
        cnf.append([-s[u], e0] + nb)
        ends += [e1, e0]
    for cl in CardEnc.atmost(ends, bound=2 * c, vpool=pool, encoding=EncType.seqcounter).clauses:
        cnf.append(cl)
    for cl in CardEnc.atleast(s, bound=L, vpool=pool, encoding=EncType.seqcounter).clauses:
        cnf.append(cl)
    # symmetry: vertex 0 selected
    cnf.append([s[0]])
    t0 = time.time()
    rounds = 0
    with Solver(name='cadical153', bootstrap_with=cnf.clauses) as sol:
        while time.time() - t0 < tmax:
            if not sol.solve():
                return 'UNSAT', None, rounds
            mdl = sol.get_model()
            sel = {u for u in range(V) if mdl[s[u] - 1] > 0}
            cyc = cycles(sel, m)
            if not cyc:
                return 'SAT', sorted(sel), rounds
            for cy in cyc:
                sol.add_clause([-s[u] for u in cy])
            rounds += 1
    return 'UNKNOWN', None, rounds


def cycles(sel, m):
    adj = {u: [u ^ (1 << i) for i in range(m) if u ^ (1 << i) in sel] for u in sel}
    seen, out = set(), []
    for u in sel:
        if u in seen:
            continue
        comp, st = [], [u]; seen.add(u)
        while st:
            a = st.pop(); comp.append(a)
            for b in adj[a]:
                if b not in seen:
                    seen.add(b); st.append(b)
        if all(len(adj[a]) == 2 for a in comp):
            out.append(comp)
    return out


def components(sel, m):
    sel = set(sel)
    e = sum(1 for u in sel for i in range(m) if u ^ (1 << i) in sel) // 2
    return len(sel) - e


if __name__ == '__main__':
    m, c, L = map(int, sys.argv[1:4])
    tmax = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    st, sel, r = search(m, c, L, tmax)
    print('m=%d c<=%d |F|>=%d : %s (cut rounds %d)' % (m, c, L, st, r), flush=True)
    if sel:
        print(' witness: |F|=%d paths=%d' % (len(sel), components(sel, m)))
        print(json.dumps(sel))
