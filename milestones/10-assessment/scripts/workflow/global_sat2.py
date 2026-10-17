"""Global SAT + lazy cycle elimination (CEGAR) for 'no induced path with T vertices in Q_n'.
Usage: python global_sat.py N T TIMEOUT [solver]
Encoding: x_v selected, e_v endpoint; induced degree 1 (endpoints) or 2 (others); exactly two
endpoints; sum x >= T; parity balance; symmetry breaking: 0 endpoint, path starts 0,1,3,7.
Each SAT model containing induced cycles gets one 'not all of this cycle' clause per cycle."""
import sys, json, time, threading
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

n, T, timeout = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
sname = sys.argv[4] if len(sys.argv) > 4 else 'cadical195'
prefix = [int(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else None
V = 1 << n
pool = IDPool()
x = {v: pool.id(('x', v)) for v in range(V)}
e = {v: pool.id(('e', v)) for v in range(V)}
cl = []
for v in range(V):
    nb = [v ^ (1 << k) for k in range(n)]
    cl.append([-e[v], x[v]])
    cl.append([-x[v]] + [x[w] for w in nb])
    for a, b, c in combinations(nb, 3):
        cl.append([-x[v], -x[a], -x[b], -x[c]])
    for a, b in combinations(nb, 2):
        cl.append([-e[v], -x[a], -x[b]])
    for a in nb:
        cl.append([-x[v], e[v]] + [x[b] for b in nb if b != a])
ends = [e[v] for v in range(V)]
cl += CardEnc.equals(lits=ends, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses
cl += CardEnc.atleast(lits=[x[v] for v in range(V)], bound=T, vpool=pool, encoding=EncType.totalizer).clauses
ev = [x[v] for v in range(V) if bin(v).count('1') % 2 == 0]
od = [x[v] for v in range(V) if bin(v).count('1') % 2 == 1]
# |even - odd| <= 1 with total >= T: at least floor(T/2) of each parity... use: each side >= (T-1)//2
cl += CardEnc.atleast(lits=ev, bound=(T - 1) // 2, vpool=pool, encoding=EncType.totalizer).clauses
cl += CardEnc.atleast(lits=od, bound=(T - 1) // 2, vpool=pool, encoding=EncType.totalizer).clauses
if prefix is None:
    for v in (0, 1, 3, 7):
        if v < V:
            cl.append([x[v]])
    cl.append([e[0]])
else:
    pset = set(prefix)
    for v in prefix:
        cl.append([x[v]])
    cl.append([e[prefix[0]]])
    for i, v in enumerate(prefix[:-1]):
        for k in range(n):
            w = v ^ (1 << k)
            if w not in pset:
                cl.append([-x[w]])
    for v in prefix[1:-1]:
        cl.append([-e[v]])
s = Solver(name=sname, bootstrap_with=cl)
t0 = time.time(); iters = 0; cuts = 0; status = None
deadline = t0 + timeout
while True:
    rem = deadline - time.time()
    if rem <= 0:
        status = 'UNKNOWN'; break
    timer = threading.Timer(rem, lambda: s.interrupt()); timer.start()
    r = s.solve_limited(expect_interrupt=True); timer.cancel()
    iters += 1
    if r is None:
        status = 'UNKNOWN'; break
    if r is False:
        status = 'UNSAT'; break
    m = set(l for l in s.get_model() if l > 0)
    sel = {v for v in range(V) if x[v] in m}
    seen = set(); comps = []
    for v in sel:
        if v in seen: continue
        comp, st = [], [v]; seen.add(v)
        while st:
            u = st.pop(); comp.append(u)
            for k in range(n):
                w = u ^ (1 << k)
                if w in sel and w not in seen:
                    seen.add(w); st.append(w)
        comps.append(comp)
    cyc = [c for c in comps if 0 not in c]
    if not cyc:
        status = 'SNAKE_FOUND'; break
    for c in cyc:
        s.add_clause([-x[v] for v in c]); cuts += 1
el = time.time() - t0
st = s.accum_stats()
print(json.dumps(dict(prefix_len=len(prefix) if prefix else 0, n=n, T=T, solver=sname, status=status, seconds=round(el, 2), cegar_iters=iters,
                      cycle_cuts=cuts, vars=pool.top, clauses=len(cl), conflicts=st.get('conflicts'))), flush=True)
