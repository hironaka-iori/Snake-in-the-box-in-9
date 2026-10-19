"""Counterexample-guided refinement of the direction-aware count automaton.

Abstraction.  A path is read as transition directions d_1, d_2, ... and
internal singleton counts.  A state remembers the last L directions (up to
relabelling) and the last k-1 counts; counts above K are lumped into the
symbol K+1, meaning the range K+1..21.  A transition appends one direction
and one count.  It is allowed unless

  * the last L+1 directions do not form an induced path segment, or
  * some window of c = 2..k consecutive internal centers ending at the new
    vertex is *known* to be infeasible in the local radius-r model.

Untested windows are allowed, so the abstraction over-approximates real
snakes and its minimum cycle mean is a valid lower bound for the average
internal count (given the window exclusions it uses).

Refinement.  Howard's policy iteration finds a minimum-mean cycle.  Every
window on it is sent to the SAT oracle (wincert.Encoding).  Infeasible
windows are added and the cycle disappears.  When every window on the
minimum cycle is feasible, the abstraction is tight for this (L, k, K, r).

  python refine.py --L 7 --k 4 --K 5 --radius 3
"""
import argparse, itertools, json, os, time
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
from wincert import Encoding, decide, window_from_dirs, cycles_of

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, '..', 'data')
CACHE = os.environ.get('ORACLE_CACHE', os.path.join(DATA, 'oracle_cache.jsonl'))
# cycle cuts found by the oracle, per (canonical direction shape, radius): valid for every window
# of that shape, so each query starts with them (see certify_direction.py)
CUT_STORE = os.environ.get('ORACLE_CUTS', os.path.join(DATA, 'cycle_cuts_oracle.json'))


def load_cuts(path):
    out = {}
    if path and os.path.exists(path):
        try:
            for k, v in json.load(open(path)).items():
                dirs, radius = k.rsplit('/', 1)
                out[(tuple(int(x) for x in dirs.split(',')), int(radius))] = [tuple(c) for c in v]
        except ValueError:
            pass
    return out


def save_cuts(path, cuts):
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump({','.join(map(str, d)) + '/' + str(r): v for (d, r), v in cuts.items() if v}, f)
    os.replace(tmp, path)


def merge_cuts(cuts, key, new):
    if new:
        known = cuts.setdefault(key, [])
        have = set(known)
        known.extend(c for c in map(tuple, new) if c not in have)


def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def induced(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ (1 << d))
    return len(set(vs)) == len(vs) and all(bin(vs[i] ^ vs[j]).count('1') != 1
                                           for i in range(len(vs)) for j in range(i + 2, len(vs)))


def key(ds, al):
    """Canonical key of a window: directions and count ranges, up to relabelling and reversal."""
    al = tuple(a if isinstance(a, tuple) else (a, a) for a in al)
    f = (canon(ds), al)
    r = (canon(tuple(reversed(ds))), tuple(reversed(al)))
    return min(f, r)


class Oracle:
    def __init__(self, radius):
        self.radius = radius
        self.known = {}
        self.cuts = load_cuts(CUT_STORE)
        import glob
        for path in sorted(glob.glob(os.path.join(DATA, 'oracle_cache*.jsonl'))):
            for line in open(path):
                try:
                    e = json.loads(line)
                except ValueError:
                    continue
                if e.get('radius') == radius and 'alpha' in e:          # omega caches carry 'buckets'
                    self.known[(tuple(e['dirs']), tuple(map(tuple, e['alpha'])))] = e['status']
        self.seed_from_surveys()

    def seed_from_surveys(self):
        for fn in ('survey_c3_r3.json', 'survey_c4_r3_k5.json'):
            p = os.path.join(DATA, fn)
            if self.radius != 3 or not os.path.exists(p):
                continue
            for r in json.load(open(p))['results']:
                k = key(tuple(r['directions']), tuple(r['alpha']))
                self.known.setdefault(k, r['status'])

    def status(self, k):
        return self.known.get(k)

    def query(self, keys, workers=4, timeout=None, verbose=True):
        keys = [k for k in set(keys) if k not in self.known]
        if not keys:
            return 0
        if verbose:
            print(f'  querying {len(keys)} windows', flush=True)
        # each answer is appended to the cache as soon as it arrives, so an interrupted batch
        # (the cloud machine restarts) keeps everything already decided
        pool = _shared_pool(workers) if timeout is None else None
        args = [(k, self.radius, self.cuts.get((k[0], self.radius), [])) for k in keys]
        with open(CACHE, 'a', buffering=1) as f:
            def record(res):
                k, st, secs = res[:3]
                self.known[k] = st
                if len(res) > 3:
                    merge_cuts(self.cuts, (k[0], self.radius), res[3])
                f.write(json.dumps({'dirs': list(k[0]), 'alpha': [list(a) for a in k[1]],
                                    'radius': self.radius, 'status': st, 'seconds': secs}) + '\n')
            if timeout is None:
                for res in pool.imap_unordered(_solve, args):
                    record(res)
            else:
                # hard per-query time limit (CaDiCaL cannot be interrupted, so each query runs in
                # its own process and is killed at the limit): windows that are expensive to refute
                # are recorded as UNKNOWN (treated as feasible), so only cheap certificates are needed
                for res in run_limited(args, workers, timeout):
                    record(res)
        save_cuts(CUT_STORE, self.cuts)
        return len(keys)


def _child(arg, conn):
    try:
        conn.send(_solve(arg))
    except Exception:
        conn.send(None)
    conn.close()


def run_limited(args, workers, timeout):
    """Run _solve on every arg in at most `workers` processes from a forkserver (cheap to start,
    independent of the size of the calling process); a query running longer than `timeout`
    seconds is killed and reported as UNKNOWN.  Yields (key, status, seconds) as they finish."""
    import multiprocessing as mp
    from multiprocessing.connection import wait
    ctx = mp.get_context('forkserver')
    pending = list(args)[::-1]
    running = {}
    while pending or running:
        while pending and len(running) < workers:
            a = pending.pop()
            r, w = ctx.Pipe(duplex=False)
            p = ctx.Process(target=_child, args=(a, w))
            p.start(); w.close()
            running[p] = (a, r, time.time())
        ready = wait([v[1] for v in running.values()], timeout=0.25)
        now = time.time()
        for p, (a, r, t0) in list(running.items()):
            if r in ready:
                try:
                    res = r.recv()
                except EOFError:
                    res = None
                p.join(); r.close(); del running[p]
                yield res if res else (a[0], 'UNKNOWN', round(now - t0, 2))
            elif now - t0 > timeout:
                p.kill(); p.join(); r.close(); del running[p]
                yield a[0], 'UNKNOWN', round(timeout, 2)


_POOL = [None, 0]


def _shared_pool(workers):
    """One worker pool for all queries of a run (forking a large refinement process per small
    batch costs more than the queries themselves)."""
    if _POOL[0] is None or _POOL[1] != workers:
        _reset_pool()
        _POOL[0], _POOL[1] = Pool(workers), workers
    return _POOL[0]


def _reset_pool():
    if _POOL[0] is not None:
        _POOL[0].terminate(); _POOL[0].join()
        _POOL[0] = None


class TwoLevelOracle(Oracle):
    """Radius `radius` first; windows feasible (or undecided) there are decided again in the
    larger ball of radius `up`.  Both models consist of necessary conditions on a snake, so a
    refutation at either radius excludes the window; `level(k)` names the radius that refutes it."""

    def __init__(self, radius=3, up=4):
        super().__init__(radius)
        self.up = up
        self.base = dict(self.known)                        # statuses at the base radius
        self.upper = Oracle.__new__(Oracle)                 # an Oracle at the larger radius
        self.upper.radius = up
        self.upper.known = {}
        self.upper.cuts = self.cuts                         # keys carry the radius
        import glob
        for path in sorted(glob.glob(os.path.join(DATA, 'oracle_cache*.jsonl'))):
            for line in open(path):
                try:
                    e = json.loads(line)
                except ValueError:
                    continue
                if e.get('radius') == up and 'alpha' in e:
                    self.upper.known[(tuple(e['dirs']), tuple(map(tuple, e['alpha'])))] = e['status']
        for k, st in self.upper.known.items():
            if st == 'UNSAT' and self.known.get(k) != 'AVOID':
                self.known[k] = 'UNSAT'

    def level(self, k):
        if self.base.get(k) == 'UNSAT':
            return self.radius
        if self.upper.known.get(k) == 'UNSAT':
            return self.up
        return None

    def escalatable(self, k):
        return self.known.get(k) in ('SAT', 'UNKNOWN') and k not in self.upper.known

    def query(self, keys, workers=4, timeout=None, verbose=True, escalate=True):
        keys = list(set(keys))
        before = {k: self.known.get(k) for k in keys}
        n = Oracle.query(self, keys, workers, timeout, verbose)
        for k in keys:
            if before[k] is None and k in self.known:
                self.base[k] = self.known[k]
        esc = [k for k in keys if self.escalatable(k)] if escalate else []
        if esc:
            if verbose:
                print(f'  escalating {len(esc)} windows to radius {self.up}', flush=True)
            n += self.upper.query(esc, workers, timeout, verbose=False)
            for k in esc:
                if self.upper.known.get(k) == 'UNSAT':
                    self.known[k] = 'UNSAT'
        return n


def _solve(arg):
    """Decide one window; the cycle cuts already known for its shape are added before the first
    solve.  Returns (key, status, seconds, new cuts)."""
    (ds, al), radius = arg[:2]
    pre = arg[2] if len(arg) > 2 else []
    t = time.time()
    enc = Encoding(window_from_dirs(ds), [a if a[0] != a[1] else a[0] for a in al], radius)
    for c in pre:
        enc.add_cycle_cut(c)
    from pysat.solvers import Cadical153
    found, st = [], 'UNSAT'
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while s.solve():
            model = s.get_model()
            sel = [v for v in enc.ball if model[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                st = 'SAT'; break
            if len(found) > 10000:
                st = 'UNKNOWN'; break
            for c in cyc:
                enc.add_cycle_cut(c); s.add_clause(enc.clauses[-1])
                found.append(tuple(sorted(c)))
    return (ds, al), st, round(time.time() - t, 2), found


class Automaton:
    def __init__(self, L, k, K):
        self.L, self.k, self.K = L, k, K
        self.sym = list(range(1, K + 2))           # K+1 means K+1..21
        self.dstates = sorted({canon(ds) for ds in itertools.product(range(L), repeat=L)
                               if induced(canon(ds))})
        self.dtrans = {}
        for c in self.dstates:
            out = []
            for d in range(min(max(c) + 2, 9)):
                ds = c + (d,)
                if induced(ds):
                    out.append((ds, canon(ds[1:])))
            self.dtrans[c] = out
        self.astates = list(itertools.product(self.sym, repeat=k - 1))
        self.sid = {}
        for c in self.dstates:
            for a in self.astates:
                self.sid[(c, a)] = len(self.sid)
        self.n = len(self.sid)

    def rng(self, s):
        return (s, s) if s <= self.K else (self.K + 1, 21)

    def windows(self, ds_ext, alphas):
        """Window keys ending at the newest center: c centers use the last c+1 directions."""
        out = []
        for c in range(2, self.k + 1):
            out.append(key(ds_ext[-(c + 1):], tuple(self.rng(s) for s in alphas[-c:])))
        return out

    def edges(self, oracle):
        """Allowed edges (u, v, w, windows) where w is the lower value of the new count."""
        U, V, W, WIN = [], [], [], []
        for (c, a), u in self.sid.items():
            for ds_ext, nc in self.dtrans[c]:
                for s in self.sym:
                    al = a + (s,)
                    ws = self.windows(ds_ext, al)
                    if any(oracle.status(x) == 'UNSAT' for x in ws):
                        continue
                    U.append(u); V.append(self.sid[(nc, al[1:])]); W.append(s); WIN.append(ws)
        return np.array(U), np.array(V), np.array(W), WIN


def prune(n, U, V):
    """Keep edges between nodes lying on some infinite walk (every node needs an out-edge)."""
    alive = np.ones(n, bool)
    while True:
        m = alive[U] & alive[V]
        out = np.bincount(U[m], minlength=n) > 0
        new = alive & out
        inn = np.bincount(V[m & new[U]], minlength=n) > 0
        new &= inn
        if (new == alive).all():
            return m
        alive = new


def howard(n, U, V, W, iters=200):
    """Minimum cycle mean by policy iteration (floats); returns (mean, cycle edge ids)."""
    order = np.argsort(U, kind='stable')
    U, V, W = U[order], V[order], W[order].astype(float)
    starts = np.searchsorted(U, np.arange(n))
    has = np.bincount(U, minlength=n) > 0
    pol = np.full(n, -1)
    pol[has] = starts[has]
    for _ in range(iters):
        # evaluate the functional graph of the policy
        nxt = V[pol]; cost = W[pol]
        eta = np.full(n, np.nan); val = np.zeros(n)
        state = np.zeros(n, np.int8)
        for s0 in range(n):
            if state[s0] or pol[s0] < 0:
                continue
            path = []; x = s0
            while state[x] == 0:
                state[x] = 1; path.append(x); x = nxt[x]
            if state[x] == 1:                       # new cycle
                i = path.index(x); cyc = path[i:]
                mu = sum(cost[y] for y in cyc) / len(cyc)
                for y in cyc:
                    eta[y] = mu
                val[x] = 0.0
                for y in reversed(cyc[1:]):
                    val[y] = cost[y] - mu + val[nxt[y]]
                tail = path[:i]
            else:
                tail = path
            for y in reversed(tail):
                eta[y] = eta[nxt[y]]; val[y] = cost[y] - eta[y] + val[nxt[y]]
            for y in path:
                state[y] = 2
        # improve
        e_eta = eta[V]; e_val = W - e_eta + val[V]
        changed = False
        best = pol.copy()
        for u in range(n):
            if pol[u] < 0:
                continue
            lo, hi = starts[u], starts[u + 1] if u + 1 < n else len(U)
            seg_eta = e_eta[lo:hi]
            m = seg_eta.min()
            if m < eta[u] - 1e-9:
                best[u] = lo + int(np.argmin(seg_eta)); changed = True
                continue
            cand = np.where(np.abs(seg_eta - eta[u]) < 1e-9)[0]
            j = cand[np.argmin(e_val[lo:hi][cand])]
            if e_val[lo + j] < val[u] - 1e-9:
                best[u] = lo + j; changed = True
        pol = best
        if not changed:
            break
    u0 = int(np.nanargmin(eta)); mu = eta[u0]
    # extract the cycle reached from u0
    seen = {}; x = u0; seq = []
    while x not in seen:
        seen[x] = len(seq); seq.append(x); x = V[pol[x]]
    cyc = seq[seen[x]:]
    return mu, [order[pol[y]] for y in cyc]


def exact_check(n, U, V, W, p, q):
    """Integer Bellman-Ford for weights q*w - p.  Returns potentials if no negative cycle."""
    w = q * W.astype(np.int64) - p
    pi = np.zeros(n, np.int64)
    for _ in range(n + 1):
        cand = pi[U] + w
        new = pi.copy()
        np.minimum.at(new, V, cand)
        if (new == pi).all():
            return pi
        pi = new
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--rounds', type=int, default=200)
    a = ap.parse_args()
    oracle = Oracle(a.radius)
    A = Automaton(a.L, a.k, a.K)
    print('states', A.n, flush=True)
    log = []
    for rnd in range(a.rounds):
        t = time.time()
        U, V, W, WIN = A.edges(oracle)
        m = prune(A.n, U, V)
        idx = np.nonzero(m)[0]
        mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
        cyc = [idx[e] for e in cyc]
        exact = Fr(int(W[cyc].sum()), len(cyc))
        wins = [x for e in cyc for x in WIN[e]]
        newq = oracle.query(wins)
        unsat = [x for x in set(wins) if oracle.status(x) == 'UNSAT']
        print(f'round {rnd}: edges {len(idx)} mean {exact} ({mu:.4f}) cycle {list(W[cyc])} '
              f'queried {newq} unsat-on-cycle {len(unsat)} [{time.time()-t:.0f}s]', flush=True)
        log.append({'round': rnd, 'mean': str(exact), 'cycle_counts': [int(x) for x in W[cyc]],
                    'queried': newq, 'killed': len(unsat)})
        if not unsat:
            break
    pi = exact_check(A.n, U[idx], V[idx], W[idx], exact.numerator, exact.denominator)
    forb = sorted(k2 for k2, st in oracle.known.items() if st == 'UNSAT')
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(exact),
           'exact_potential_found': pi is not None,
           'potential_range': int(pi.max() - pi.min()) if pi is not None else None,
           'final_cycle_counts': [int(x) for x in W[cyc]], 'rounds': log}
    json.dump(out, open(os.path.join(DATA, f'refine_L{a.L}_k{a.k}_K{a.K}_r{a.radius}.json'), 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'rounds'}))


if __name__ == '__main__':
    main()
