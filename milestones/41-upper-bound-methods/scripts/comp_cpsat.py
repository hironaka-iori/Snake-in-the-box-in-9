"""Lower bounds on the locality ceiling h_{n,k}: maximise |S| over induced subgraphs S of Q_n that
are vertex- and edge-disjoint unions of `ncyc` induced cycles, each using at least `span`
coordinate directions, and `npath` induced paths (no edges between components).
Every component is one AddCircuit (cycles: optional nodes; paths: through a dummy node).
mode 'fibre': with npath=0, ncyc=2 the two cycles A,B give the fibre set
    S = {(x,y) : x in A if |y| even, x in B if |y| odd}  in Q_m x Q_{n-m}, of size 2^(n-m-1)(|A|+|B|).
usage: python3 comp_cpsat.py n ncyc npath span seconds workers [hint_lower]
"""
import sys, time
from ortools.sat.python import cp_model

def build(n, ncyc, npath, span, lower=0, fibre=False):
    N = 1 << n
    m = cp_model.CpModel()
    comps = ncyc + npath
    s = [[m.NewBoolVar(f"s{c}_{u}") for u in range(N)] for c in range(comps)]
    for u in range(N):
        m.AddAtMostOne([s[c][u] for c in range(comps)])
    for c in range(comps):
        isp = c >= ncyc
        arcs = []
        dirs = [[] for _ in range(n)]
        X = {}
        for u in range(N):
            arcs.append((u, u, s[c][u].Not()))
            if isp:
                st = m.NewBoolVar(""); en = m.NewBoolVar("")
                arcs += [(N, u, st), (u, N, en)]
                m.AddImplication(st, s[c][u]); m.AddImplication(en, s[c][u])
            for i in range(n):
                w = u ^ (1 << i)
                x = m.NewBoolVar("")
                arcs.append((u, w, x)); dirs[i].append(x); X[u, w] = x
                m.AddImplication(x, s[c][u]); m.AddImplication(x, s[c][w])
        m.AddCircuit(arcs)
        for u in range(N):
            for i in range(n):
                w = u ^ (1 << i)
                if u < w:
                    m.AddBoolOr([s[c][u].Not(), s[c][w].Not(), X[u, w], X[w, u]])
        if not isp:
            m.Add(sum(s[c]) >= 8)
            used = []
            for i in range(n):
                b = m.NewBoolVar(""); m.AddBoolOr(dirs[i]).OnlyEnforceIf(b); used.append(b)
                m.Add(sum(dirs[i]) == 0).OnlyEnforceIf(b.Not())
            m.Add(sum(used) >= span)
        comp_arcs = {}
    # induced: two adjacent selected vertices must be consecutive on the same component.
    # arc variables were not stored per pair; rebuild via degree argument: in a circuit each
    # selected vertex has exactly 2 incident used arcs; forbid any third selected neighbour
    # by counting selected neighbours <= 2 (cycle) / <= 2 (path, endpoints have 1 path-nbr but
    # the dummy arcs make degree 2): we require #selected neighbours (any component) == path
    # degree, enforced as: sum over neighbours of selected <= 2, and for vertices adjacent across
    # different components, forbidden.
    for u in range(N):
        anysel = [s[c][u] for c in range(comps)]
        for i in range(n):
            w = u ^ (1 << i)
            if u < w:
                for c in range(comps):
                    for d in range(comps):
                        if c != d and not fibre:
                            m.AddBoolOr([s[c][u].Not(), s[d][w].Not()])
    return m, s

def validate(n, comps, ncyc, span, fibre=False):
    allv = set()
    for C in comps:
        assert not (allv & set(C)); allv |= set(C)
    for ci, C in enumerate(comps):
        S = set(C)
        for u in C:
            for i in range(n):
                w = u ^ (1 << i)
                assert fibre or w not in allv or w in S          # no edges between components
        deg = {u: sum((u ^ (1 << i)) in S for i in range(n)) for u in S}
        ends = [u for u in S if deg[u] == 1]
        assert all(1 <= d <= 2 for d in deg.values())
        start = ends[0] if ends else C[0]
        seen = [start]; prev = None; cur = start; used = 0
        while True:
            nx = [w for w in (cur ^ (1 << i) for i in range(n)) if w in S and w != prev and w not in seen]
            if not nx: break
            used |= cur ^ nx[0]; prev, cur = cur, nx[0]; seen.append(cur)
        assert len(seen) == len(S)
        if ci < ncyc:
            assert not ends and (cur ^ start).bit_count() == 1
            used |= cur ^ start
            assert bin(used).count("1") >= span
        else:
            assert len(ends) == 2
    return len(allv)

if __name__ == "__main__":
    n, ncyc, npath, span, sec, wk = map(int, sys.argv[1:7])
    fibre = len(sys.argv) > 7 and sys.argv[7] == 'fibre'
    m, s = build(n, ncyc, npath, span, fibre=fibre)
    N = 1 << n
    tot = sum(s[c][u] for c in range(ncyc + npath) for u in range(N))
    m.Maximize(tot)
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = sec; sol.parameters.num_workers = wk
    t = time.time(); st = sol.Solve(m)
    print(f"fibre={int(fibre)} n={n} ncyc={ncyc} npath={npath} span={span} status={sol.StatusName(st)} best={sol.ObjectiveValue():.0f} bound={sol.BestObjectiveBound():.0f} wall={time.time()-t:.0f}", flush=True)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        comps = [[u for u in range(N) if sol.Value(s[c][u])] for c in range(ncyc + npath)]
        print("validated size", validate(n, comps, ncyc, span, fibre), "COMPONENTS", comps, flush=True)
