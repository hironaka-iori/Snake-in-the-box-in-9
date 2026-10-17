"""Cutting-plane loop over k-centre alpha windows (k=5 default):
min-mean cycle under current exclusions -> test its windows (radius r, all oriented shapes) -> exclude
windows infeasible for every shape -> repeat.  UNKNOWN counts as feasible (conservative)."""
import sys, json, time, itertools, os
sys.dont_write_bytecode = True
from concurrent.futures import ProcessPoolExecutor, as_completed
from mincycle import min_mean_cycle, sym, BASE2
from shapes import induced_ok, relabel
import winmin

def oriented_shapes(m):
    res = []
    def rec(ts, nlab):
        if len(ts) == m:
            res.append(tuple(ts)); return
        for t in range(min(nlab + 1, 9)):
            if ts and t == ts[-1]:
                continue
            ts.append(t)
            if induced_ok(ts):
                rec(ts, max(nlab, t + 1))
            ts.pop()
    rec([], 0)
    return res

def canon(w):
    return min(tuple(w), tuple(reversed(w)))

def test_window(w, radius, secs, pool, shapes):
    futs = {pool.submit(winmin.solve, list(s), radius, secs, list(w), False): s for s in shapes}
    status = {}
    for f in as_completed(futs):
        r = f.result()
        status[futs[f]] = r['status'] if r['best'] is None else 'FEASIBLE'
    if all(v == 'INFEASIBLE' for v in status.values()):
        return 'INFEASIBLE', status
    if any(v == 'FEASIBLE' for v in status.values()):
        return 'FEASIBLE', status
    return 'UNKNOWN', status

if __name__ == '__main__':
    k = int(sys.argv[1]); radius = int(sys.argv[2]); secs = float(sys.argv[3]); K = int(sys.argv[4])
    out = sys.argv[5]
    r3 = json.load(open('/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana/patterns_r3_s9.json'))
    st = {}
    for r in r3:
        st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
    excl3 = {p for p, s in st.items() if all(x == 'INFEASIBLE' for x in s.values())}
    forb = sym(BASE2) | sym(excl3)
    shapes = oriented_shapes(k + 1)
    print('oriented shapes:', len(shapes), flush=True)
    log = dict(k=k, radius=radius, secs=secs, K=K, rounds=[], tested={})
    if os.path.exists(out):
        log = json.load(open(out))
        for w, s in log['tested'].items():
            if s == 'INFEASIBLE':
                forb |= sym({tuple(json.loads(w))})
    with ProcessPoolExecutor(4) as pool:
        while True:
            t0 = time.time()
            lam, (mean, cyc) = min_mean_cycle(k, K, forb)
            L = len(cyc)
            wins = {canon([cyc[(i + j) % L] for j in range(k)]) for i in range(L)}
            print('min mean', lam, 'cycle', cyc, 'windows', sorted(wins), '(%.0fs)' % (time.time() - t0), flush=True)
            rnd = dict(mean=str(lam), cycle=cyc, windows=[list(w) for w in sorted(wins)], results={})
            new = [w for w in sorted(wins) if json.dumps(list(w)) not in log['tested']]
            if not new or any(K in w for w in new):
                rnd['stop'] = 'all windows tested feasible/unknown' if not new else 'cap value in window'
                log['rounds'].append(rnd); json.dump(log, open(out, 'w'), indent=1)
                print('STOP:', rnd['stop'], flush=True)
                break
            for w in new:
                t1 = time.time()
                s, det = test_window(w, radius, secs, pool, shapes)
                log['tested'][json.dumps(list(w))] = s
                rnd['results'][json.dumps(list(w))] = s
                print('   window', w, s, '%.0fs' % (time.time() - t1), flush=True)
                if s == 'INFEASIBLE':
                    forb |= sym({w})
            log['rounds'].append(rnd); json.dump(log, open(out, 'w'), indent=1)
