"""Solve fixed-prefix (cube) instances with the repo's regrowth CNF + lazy cycle cuts (CEGAR).
Usage: python sat_cube.py PREFIXFILE TIMEOUT [TOTAL=193] [START] [COUNT]
PREFIXFILE lines: 'weight d v0 ... v_{d-1}' (from ./probe) or bank form 'bank ENTRY REV KEEP'."""
import sys, json, time, threading
sys.path.insert(0, '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf')
from regrowth_cnf_copy import encode
from pysat.solvers import Solver

fn, timeout = sys.argv[1], float(sys.argv[2])
total = int(sys.argv[3]) if len(sys.argv) > 3 else 193
start = int(sys.argv[4]) if len(sys.argv) > 4 else 0
count = int(sys.argv[5]) if len(sys.argv) > 5 else 10**9
bank = None
lines = [l.split() for l in open(fn) if l.strip()][start:start + count]
for parts in lines:
    if parts[0] == 'bank':
        if bank is None:
            bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
        e, rev, keep = int(parts[1]), int(parts[2]), int(parts[3])
        p = bank[e]['vertex_sequence'][::-1] if rev else bank[e]['vertex_sequence']
        prefix, w, tag = p[:keep], None, f'bank{e}_{rev}'
    else:
        w, d = float(parts[0]), int(parts[1])
        prefix, keep, tag = [int(x) for x in parts[2:2 + d]], d, 'probe'
    data = encode(prefix, keep=keep, total_vertices=total)
    sel = data['selected']; inv = {i: v for v, i in sel.items()}
    s = Solver(name='cadical195', bootstrap_with=data['clauses'])
    t0 = time.time(); deadline = t0 + timeout; cuts = 0; iters = 0; status = None
    while True:
        rem = deadline - time.time()
        if rem <= 0:
            status = 'UNKNOWN'; break
        timer = threading.Timer(rem, lambda: s.interrupt()); timer.start()
        r = s.solve_limited(expect_interrupt=True); timer.cancel(); iters += 1
        if r is None:
            status = 'UNKNOWN'; break
        if r is False:
            status = 'UNSAT'; break
        m = set(l for l in s.get_model() if l > 0)
        chosen = {inv[i] for i in m if i in inv}
        seen, comps = set(), []
        for v in chosen:
            if v in seen: continue
            comp, st = [], [v]; seen.add(v)
            while st:
                u = st.pop(); comp.append(u)
                for k in range(9):
                    x = u ^ (1 << k)
                    if x in chosen and x not in seen:
                        seen.add(x); st.append(x)
            comps.append(comp)
        cyc = [c for c in comps if data['head'] not in c]
        if not cyc:
            status = 'SNAKE_CANDIDATE'; break
        for c in cyc:
            s.add_clause([-sel[v] for v in c]); cuts += 1
    el = time.time() - t0
    st = s.accum_stats(); s.delete()
    print(json.dumps(dict(tag=tag, weight=w, keep=keep, total=total, status=status, seconds=round(el, 2),
                          conflicts=st.get('conflicts'), cegar_iters=iters, cycle_cuts=cuts,
                          region=len(data['vertices']))), flush=True)
