"""Exact global model of 'an induced path with >= V vertices in Q_n' for CP-SAT.

Connectivity is exact through AddCircuit with a dummy node (node 2^n) and optional nodes
(self-loop literal = vertex not selected).  Induced: two selected adjacent vertices must be
joined by a path arc.  Symmetry breaking (valid for V >= 3): vertex 0 and its neighbours e0, e1
are selected (an internal vertex and its two path neighbours, after translation and a coordinate
permutation); the stabiliser still permutes coordinates {0,1} and {2..n-1}, so the direction
counts are sorted: n_0 >= n_1 and n_2 >= ... >= n_{n-1}.
usage: python3 snake_cpsat.py n V seconds workers [sort=1]
Prints status and wall time; on FEASIBLE validates the path independently.
"""
import sys, time
from ortools.sat.python import cp_model

def build(n, V, sort=True, extra=None):
    N = 1 << n
    m = cp_model.CpModel()
    s = [m.NewBoolVar(f"s{u}") for u in range(N)]
    arcs = []
    a = {}
    for u in range(N):
        arcs.append((u, u, s[u].Not()))
        st = m.NewBoolVar(f"b{u}"); en = m.NewBoolVar(f"e{u}")
        arcs.append((N, u, st)); arcs.append((u, N, en))
        m.AddImplication(st, s[u]); m.AddImplication(en, s[u])
        for i in range(n):
            w = u ^ (1 << i)
            a[u, w] = m.NewBoolVar(f"a{u}_{w}")
            arcs.append((u, w, a[u, w]))
    m.AddCircuit(arcs)
    cnt = [[] for _ in range(n)]
    for u in range(N):
        for i in range(n):
            w = u ^ (1 << i)
            if u < w:
                y = m.NewBoolVar(f"y{u}_{w}")
                m.Add(y == a[u, w] + a[w, u])
                m.AddBoolOr([s[u].Not(), s[w].Not(), y])   # induced: no chords
                cnt[i].append(y)
    m.Add(sum(s) >= V)
    for u in (0, 1, 2):
        m.Add(s[u] == 1)
    if sort:
        m.Add(sum(cnt[0]) >= sum(cnt[1]))
        for i in range(2, n - 1):
            m.Add(sum(cnt[i]) >= sum(cnt[i + 1]))
    if extra:
        extra(m, s, cnt)
    return m, s

def check(n, S):
    S = set(S)
    deg = {u: sum((u ^ (1 << i)) in S for i in range(n)) for u in S}
    ends = [u for u in S if deg[u] == 1]
    assert all(d <= 2 for d in deg.values()) and len(ends) == 2
    seen = {ends[0]}; cur = ends[0]
    while True:
        nx = [w for w in (cur ^ (1 << i) for i in range(n)) if w in S and w not in seen]
        if not nx: break
        cur = nx[0]; seen.add(cur)
    assert len(seen) == len(S)
    return True

if __name__ == "__main__":
    n, V, sec, wk = map(int, sys.argv[1:5])
    sort = len(sys.argv) <= 5 or sys.argv[5] != "0"
    m, s = build(n, V, sort)
    sol = cp_model.CpSolver()
    sol.parameters.max_time_in_seconds = sec
    sol.parameters.num_workers = wk
    t = time.time(); st = sol.Solve(m); dt = time.time() - t
    name = sol.StatusName(st)
    if name in ("FEASIBLE", "OPTIMAL"):
        S = [u for u in range(1 << n) if sol.Value(s[u])]
        check(n, S); name += f" validated v={len(S)}"
    print(f"n={n} V={V} sort={int(sort)} workers={wk} status={name} wall={dt:.1f}", flush=True)
