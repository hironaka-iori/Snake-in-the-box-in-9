"""Vectorised direction-aware automaton with counterexample-guided refinement.

Same abstraction as refine.py (state = canonical shape of the last L directions
plus the last k-1 lumped counts; a transition appends one direction label and
one count), but built for k up to 6 and ~10^5-10^6 states:

* for each (shape, next label) the allowed symbol codes are computed at once
  with numpy from per-window-shape forbidden tables (symbol tuples are base-6
  codes; a window of c centres reads the low c digits);
* minimum cycle mean by Howard's policy iteration with vectorised improvement;
* integer potentials by Bellman-Ford with `minimum.reduceat`;
* the exact vertex bound by the same reduceat dynamic program.

The oracle is wincert.Encoding at the chosen radius; answers are cached in
data/oracle_cache*.jsonl exactly as refine.py does.

  python refine_fast.py --L 7 --k 6 --K 5 --radius 3
"""
import argparse, itertools, json, os, time
from fractions import Fraction as Fr
import numpy as np
from refine import Oracle, canon, induced, key, DATA


class FastAutomaton:
    def __init__(self, L, k, K):
        assert L >= k
        self.L, self.k, self.K = L, k, K
        self.ns = K + 1                                    # symbols 1..K+1
        self.shapes = sorted({canon(ds) for ds in itertools.product(range(L), repeat=L)
                              if induced(canon(ds))})
        self.sid = {c: i for i, c in enumerate(self.shapes)}
        self.m1 = self.ns ** (k - 1)                       # count states per shape
        self.n = len(self.shapes) * self.m1
        # per (shape, d): next shape, window keys per c
        self.ext = []                                      # (shape index, d, next index, {c: (fwd shape, rev shape)})
        for i, c in enumerate(self.shapes):
            for d in range(min(max(c) + 2, 9)):
                ds = c + (d,)
                if not induced(ds):
                    continue
                nxt = self.sid[canon(ds[1:])]
                wins = {}
                for cc in range(2, k + 1):
                    sub = ds[-(cc + 1):]
                    wins[cc] = (canon(sub), canon(tuple(reversed(sub))))
                self.ext.append((i, d, nxt, ds, wins))
        # symbol codes: digits = sym-1, most significant = oldest
        self.codes = np.arange(self.ns ** k)
        self.rev = {}
        for cc in range(2, k + 1):
            n_cc = self.ns ** cc
            digs = np.array([[(x // self.ns ** j) % self.ns for j in range(cc)] for x in range(n_cc)])
            self.rev[cc] = (digs * (self.ns ** np.arange(cc - 1, -1, -1))).sum(1)   # reversed tuple code

    def window_key(self, ds, al):
        return key(ds, tuple((a, a) if a <= self.K else (a, 21) for a in al))

    def forb_tables(self, oracle):
        """Per canonical window shape, a boolean array over symbol codes (low digits = last centre)."""
        T = {}
        for (dirs, alpha), st in oracle.known.items():
            if st != 'UNSAT':
                continue
            cc = len(alpha)
            if cc < 2 or cc > self.k:
                continue
            # every symbol whose count range lies inside the certified range is excluded too
            # (symbol s <= K means count s exactly, symbol K+1 means count >= K+1)
            opts = []
            for lo, hi in alpha:
                opts.append([s for s in range(1, self.ns + 1)
                             if ((lo <= s <= hi) if s <= self.K else (lo <= s and hi >= 21))])
            if any(not o for o in opts):
                continue
            tbl = T.setdefault(dirs, np.zeros(self.ns ** cc, bool))
            for syms in itertools.product(*opts):
                code = 0
                for s in syms:
                    code = code * self.ns + (s - 1)
                tbl[code] = True
        return T

    def edges(self, oracle):
        T = self.forb_tables(oracle)
        U, V, W, EXT = [], [], [], []
        for e, (i, d, nxt, ds, wins) in enumerate(self.ext):
            allowed = np.ones(len(self.codes), bool)
            for cc, (fw, rv) in wins.items():
                sub = self.codes % (self.ns ** cc)
                if fw in T:
                    allowed &= ~T[fw][sub]
                if rv in T:
                    allowed &= ~T[rv][self.rev[cc][sub]]
            codes = self.codes[allowed]
            U.append(i * self.m1 + codes // self.ns)
            V.append(nxt * self.m1 + codes % self.m1)
            W.append(codes % self.ns + 1)
            EXT.append(np.full(len(codes), e))
        return (np.concatenate(U).astype(np.int64), np.concatenate(V).astype(np.int64),
                np.concatenate(W).astype(np.int64), np.concatenate(EXT))

    def decode(self, u, e, w):
        """State u, extension e, new symbol w -> (list of L+1 directions, list of k symbols)."""
        i, d, nxt, ds, wins = self.ext[int(e)]
        t = int(u) % self.m1
        digs = [int((t // self.ns ** j) % self.ns + 1) for j in range(self.k - 2, -1, -1)]
        return [int(x) for x in ds], digs + [int(w)]


def prune(n, U, V):
    alive = np.ones(n, bool)
    while True:
        m = alive[U] & alive[V]
        out = np.bincount(U[m], minlength=n) > 0
        inn = np.bincount(V[m], minlength=n) > 0
        new = alive & out & inn
        if (new == alive).all():
            return m
        alive = new


def howard(n, U, V, W, iters=300):
    """Minimum cycle mean (float) and the cycle (edge indices, in input numbering)."""
    order = np.argsort(U, kind='stable')
    U, V, W = U[order], V[order], W[order].astype(float)
    starts = np.searchsorted(U, np.arange(n + 1))
    has = starts[1:] > starts[:-1]
    pol = np.where(has, starts[:-1], -1)
    for _ in range(iters):
        nxt = np.where(pol >= 0, V[np.maximum(pol, 0)], -1)
        cost = np.where(pol >= 0, W[np.maximum(pol, 0)], 0.0)
        eta = np.full(n, np.inf); val = np.zeros(n)
        state = np.zeros(n, np.int8)
        all_cycles = []
        for s0 in range(n):
            if state[s0] or pol[s0] < 0:
                continue
            path = []; x = s0
            while x >= 0 and state[x] == 0:
                state[x] = 1; path.append(x); x = nxt[x]
            if x >= 0 and state[x] == 1:
                i = path.index(x); cyc = path[i:]
                mu = sum(cost[y] for y in cyc) / len(cyc)
                all_cycles.append((mu, cyc))
                for y in cyc:
                    eta[y] = mu
                val[x] = 0.0
                for y in reversed(cyc[1:]):
                    val[y] = cost[y] - mu + val[nxt[y]]
                tail = path[:i]
            else:
                tail = path
            for y in reversed(tail):
                if nxt[y] >= 0 and np.isfinite(eta[nxt[y]]):
                    eta[y] = eta[nxt[y]]; val[y] = cost[y] - eta[y] + val[nxt[y]]
            for y in path:
                state[y] = 2
        # improvement, vectorised per source segment
        e_eta = eta[V]
        e_val = W - e_eta + val[V]
        seg = starts[:-1][has]
        best_eta = np.minimum.reduceat(e_eta, seg)
        cur_eta = eta[has]
        improve_eta = best_eta < cur_eta - 1e-9
        # among edges with eta == cur eta, minimal val
        masked_val = np.where(np.abs(e_eta - np.repeat(cur_eta, np.diff(starts)[has])) < 1e-9, e_val, np.inf)
        best_val = np.minimum.reduceat(masked_val, seg)
        improve_val = (~improve_eta) & (best_val < val[has] - 1e-9)
        if not (improve_eta.any() or improve_val.any()):
            break
        newpol = pol.copy()
        hs = np.nonzero(has)[0]
        for u in hs[improve_eta | improve_val]:
            lo, hi = starts[u], starts[u + 1]
            if best_eta[np.searchsorted(hs, u)] < eta[u] - 1e-9:
                newpol[u] = lo + int(np.argmin(e_eta[lo:hi]))
            else:
                newpol[u] = lo + int(np.argmin(masked_val[lo:hi]))
        pol = newpol
    u0 = int(np.nanargmin(np.where(np.isfinite(eta), eta, np.inf))); mu = eta[u0]
    seen = {}; x = u0; seq = []
    while x not in seen:
        seen[x] = len(seq); seq.append(x); x = int(V[pol[x]])
    cyc = seq[seen[x]:]
    howard.extra = sorted(((m_, [int(order[pol[y]]) for y in c]) for m_, c in all_cycles), key=lambda t: t[0])
    return mu, [int(order[pol[y]]) for y in cyc]


def bellman_ford(n, U, V, W, p, q, max_iter=100000):
    """Integer potentials for weights q*w - p (None if a negative cycle exists)."""
    order = np.argsort(V, kind='stable')
    U, V, W = U[order], V[order], W[order]
    w = q * W - p
    starts = np.searchsorted(V, np.arange(n + 1))
    has = starts[1:] > starts[:-1]
    seg = starts[:-1][has]
    pi = np.zeros(n, np.int64)
    for it in range(max_iter):
        cand = pi[U] + w
        best = np.minimum.reduceat(cand, seg)
        new = pi.copy()
        new[has] = np.minimum(pi[has], best)
        if (new == pi).all():
            return pi
        pi = new
    return None


def vertex_bound(A, U, V, W, vmax=260):
    """Largest v with a walk realising T <= 9214 - 35 v (same accounting as direction_bound.bound)."""
    t0 = A.L - 1
    pre = t0 - (A.k - 1)
    order = np.argsort(V, kind='stable')
    U, V, W = U[order], V[order], W[order]
    starts = np.searchsorted(V, np.arange(A.n + 1))
    has = starts[1:] > starts[:-1]
    seg = starts[:-1][has]
    init = np.full(A.n, np.inf)
    digs = np.array([[(t // A.ns ** j) % A.ns + 1 for j in range(A.k - 1)] for t in range(A.m1)]).sum(1)
    for i in range(len(A.shapes)):
        init[i * A.m1:(i + 1) * A.m1] = digs
    dp = init.copy(); best = None; steps = 0
    for v in range(t0 + 2, vmax + 1):
        n = v - 2
        while steps < n - t0:
            cand = dp[U] + W
            new = np.full(A.n, np.inf)
            new[has] = np.minimum.reduceat(cand, seg)
            dp = new; steps += 1
        T = 8 + pre + dp.min()
        if T <= 9214 - 35 * v:
            best = v
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--rounds', type=int, default=300)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--slack', type=float, default=0.3, help='also query cycles with mean <= min + slack')
    ap.add_argument('--batch', type=int, default=200, help='max extra cycles per round')
    ap.add_argument('--index', help='certificate index: rebuild from these exclusions only and verify')
    ap.add_argument('--avoid', help='JSON list of {dirs, alpha} windows to treat as feasible (expensive certificates)')
    ap.add_argument('--query-timeout', type=float, default=None, help='seconds per oracle query; slower windows count as feasible')
    ap.add_argument('--out')
    a = ap.parse_args()
    if a.index:
        cases = [c for c in json.load(open(a.index))['cases'] if c['drat_trim_verified']]
        keys = [(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha'])) for c in cases]
        class Listed:
            known = {kk: 'UNSAT' for kk in keys}
            def status(self, kk): return self.known.get(kk)
        A = FastAutomaton(a.L, a.k, a.K)
        U, V, W, EXT = A.edges(Listed())
        m = prune(A.n, U, V); idx = np.nonzero(m)[0]
        mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
        lam = Fr(int(W[cyc].sum()), len(cyc))
        pi = bellman_ford(A.n, U, V, W, lam.numerator, lam.denominator)
        assert pi is not None
        slack = lam.denominator * W - lam.numerator + pi[U] - pi[V]
        assert (slack >= 0).all()
        vb = vertex_bound(A, U, V, W)
        out = {'L': a.L, 'k': a.k, 'K': a.K, 'listed_exclusions': len(keys), 'states': A.n, 'edges': int(len(U)),
               'min_mean': str(lam), 'potential_checked_on_every_edge': True,
               'potential_range': int(pi.max() - pi.min()), 'max_vertices': vb, 'max_edges': vb - 1}
        print(json.dumps(out))
        if a.out:
            json.dump(out, open(a.out, 'w'), indent=1)
        return
    oracle = Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            oracle.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    A = FastAutomaton(a.L, a.k, a.K)
    print('shapes', len(A.shapes), 'states', A.n, 'extensions', len(A.ext), flush=True)
    log = []
    for rnd in range(a.rounds):
        t = time.time()
        U, V, W, EXT = A.edges(oracle)
        m = prune(A.n, U, V)
        idx = np.nonzero(m)[0]
        mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
        cyc = [idx[e] for e in cyc]
        exact = Fr(int(W[cyc].sum()), len(cyc))
        wins = []
        batch = [c for m_, c in howard.extra if m_ <= mu + a.slack][:a.batch]
        for cyc2 in [cyc] + batch:
            for e in cyc2:
                e = idx[e] if cyc2 is not cyc else e
                ds, al = A.decode(U[e], EXT[e], W[e])
                for cc in range(2, a.k + 1):
                    wins.append(A.window_key(tuple(ds[-(cc + 1):]), tuple(al[-cc:])))
        wins = list(dict.fromkeys(wins))
        newq = oracle.query(wins, a.workers, a.query_timeout)
        unsat = [x for x in wins if oracle.status(x) == 'UNSAT']
        print(f'round {rnd}: edges {len(idx)} mean {exact} ({mu:.4f}) cycle {[int(x) for x in W[cyc]]} '
              f'queried {newq} unsat-on-cycle {len(unsat)} [{time.time()-t:.0f}s]', flush=True)
        log.append({'round': rnd, 'mean': str(exact), 'cycle_counts': [int(x) for x in W[cyc]],
                    'queried': newq, 'killed': len(unsat)})
        if not unsat:
            break
    pi = bellman_ford(A.n, U, V, W, exact.numerator, exact.denominator)
    vb = vertex_bound(A, U, V, W)
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(exact),
           'exact_potential_found': pi is not None,
           'potential_range': int(pi.max() - pi.min()) if pi is not None else None,
           'max_vertices': vb, 'max_edges': vb - 1, 'edges': int(len(U)),
           'final_cycle_counts': [int(x) for x in W[cyc]], 'rounds': log}
    json.dump(out, open(os.path.join(DATA, f'refine_L{a.L}_k{a.k}_K{a.K}_r{a.radius}.json'), 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'rounds'}))


if __name__ == '__main__':
    main()
