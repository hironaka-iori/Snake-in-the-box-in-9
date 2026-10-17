"""Generalised local-window model (same relaxation as milestones/07-window-223/scripts/local_window_search.py,
re-implemented): a k-centre window with a given transition shape, ball of radius r around the centres,
selected interior vertices have degree 2-e, sum e <= 2, boundary degree <= 2, no selected 4-cycle,
lazy cycle cuts.  Objective: minimise the sum of the centres' singleton counts (or feasibility with targets).
radius 9 => whole cube => every cycle-free solution is ONE genuine induced path (checked independently)."""
import sys, json, time, itertools
sys.dont_write_bytecode = True
from ortools.sat.python import cp_model

PAIRS = list(itertools.combinations(range(9), 2))

def comps(sel):
    S = set(sel)
    adj = {v: [v ^ 1 << k for k in range(9) if (v ^ 1 << k) in S] for v in S}
    seen = set(); out = []
    for s in S:
        if s in seen:
            continue
        st = [s]; c = []
        while st:
            v = st.pop()
            if v in seen:
                continue
            seen.add(v); c.append(v); st.extend(adj[v])
        out.append((c, len(c) > 2 and all(len(adj[v]) == 2 for v in c)))
    return out

def build(shape, radius, alpha=None, maxsum=None):
    win = [0]
    for t in shape:
        win.append(win[-1] ^ 1 << t)
    centers = win[1:-1]
    k = len(centers)
    dist = lambda v: min(bin(v ^ c).count('1') for c in centers)
    ball = [v for v in range(512) if dist(v) <= radius]
    m = cp_model.CpModel()
    x = {v: m.new_bool_var(f'x{v}') for v in ball}
    ends = []
    for v in win:
        m.add(x[v] == 1)
    for v in ball:
        nb = [v ^ 1 << q for q in range(9) if (v ^ 1 << q) in x]
        deg = sum(x[w] for w in nb)
        if len(nb) == 9:
            e = m.new_bool_var(f'e{v}'); ends.append(e)
            m.add(e <= x[v])
            m.add(deg == 2 - e).only_enforce_if(x[v])
        else:
            m.add(deg <= 2).only_enforce_if(x[v])
    m.add(sum(ends) <= 2)
    al = []
    for i, c in enumerate(centers, 1):
        used = {(c ^ win[i - 1]).bit_length() - 1, (c ^ win[i + 1]).bit_length() - 1}
        free = [(a, b) for a, b in PAIRS if a not in used and b not in used]
        assert len(free) == 21
        al.append(21 - sum(x[c ^ 1 << a ^ 1 << b] for a, b in free))
    if alpha is not None:
        for a, t in zip(al, alpha):
            m.add(a == t)
    for v in ball:
        for a, b in PAIRS:
            if v >> a & 1 or v >> b & 1:
                continue
            sq = [v, v | 1 << a, v | 1 << b, v | 1 << a | 1 << b]
            if all(w in x for w in sq):
                m.add(sum(x[w] for w in sq) <= 3)
    obj = sum(al)
    if maxsum is not None:
        m.add(obj <= maxsum)
    return m, x, ball, win, centers, obj, al

def solve(shape, radius, seconds, alpha=None, minimize=True, workers=1, seed=7, maxsum=None):
    m, x, ball, win, centers, obj, al = build(shape, radius, alpha, maxsum)
    if minimize and alpha is None:
        m.minimize(obj)
    s = cp_model.CpSolver()
    s.parameters.num_search_workers = workers
    s.parameters.random_seed = seed
    t0 = time.monotonic(); cuts = 0; best = None; status = None; bound = None
    while True:
        rem = seconds - (time.monotonic() - t0)
        if rem <= 0:
            status = 'TIMEOUT'; break
        s.parameters.max_time_in_seconds = rem
        st = s.solve(m)
        status = s.status_name(st)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            break
        sel = [v for v in ball if s.value(x[v])]
        cyc = [c for c, iscyc in comps(sel) if iscyc]
        if minimize and alpha is None:
            bound = s.best_objective_bound
        if not cyc:
            best = dict(selected=sel, alphas=[s.value(a) for a in al], sum=int(s.value(obj)))
            break
        for c in cyc:
            m.add(sum(x[v] for v in c) <= len(c) - 1); cuts += 1
    return dict(shape=list(shape), radius=radius, status=status, cuts=cuts, t=round(time.monotonic() - t0, 2),
                bound=bound, best=best, alpha_target=alpha)

if __name__ == '__main__':
    from concurrent.futures import ProcessPoolExecutor
    spec = json.loads(sys.argv[1]); out = sys.argv[2]; W = int(sys.argv[3])
    def job(a):
        return solve(*a)
    res = []
    with ProcessPoolExecutor(W) as ex:
        futs = [ex.submit(solve, *a) for a in spec]
        for f in futs:
            r = f.result()
            print({k: v for k, v in r.items() if k != 'best'}, (r['best'] or {}).get('alphas'), (r['best'] or {}).get('sum'), flush=True)
            res.append(r)
    json.dump(res, open(out, 'w'))
