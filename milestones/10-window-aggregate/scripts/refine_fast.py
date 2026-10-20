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


def greedy_break(oracle, cyc_wins, workers, timeout, chunk=None, long_timeout=None, long_max=None):
    """Query windows until every cycle contains an excluded window.  Each step asks, in parallel,
    the windows shared by the most still-unbroken cycles (fewer centres first on ties).  With
    `long_timeout`, cycles that only windows killed at the short limit could still break get
    those windows again (once each, at most `long_max` per step) with the long limit: a timeout
    is not feasibility, and a cycle kept alive by timeouts alone would end the refinement early."""
    asked = 0
    long_max = long_max or 2 * workers
    chunk = chunk or 16 * workers          # a chunk waits for its slowest window; keep the workers busy
    while True:
        alive = [i for i, cw in enumerate(cyc_wins) if not any(oracle.status(x) == 'UNSAT' for x in cw)]
        if not alive:
            print(f'  greedy: {asked} queries broke all {len(cyc_wins)} cycles', flush=True)
            return asked
        count = {}
        esc = getattr(oracle, 'escalatable', None)
        for i in alive:
            for x in cyc_wins[i]:
                if oracle.status(x) is None or (esc is not None and esc(x)):
                    count[x] = count.get(x, 0) + 1
        if not count and long_timeout:
            retried = oracle.__dict__.setdefault('retried', set())
            upper = getattr(oracle, 'upper', None)
            slow = {}
            for i in alive:
                for x in cyc_wins[i]:
                    # retry only windows no ball has decided (a timeout at every level tried)
                    if (oracle.status(x) == 'UNKNOWN' and x not in retried
                            and (upper is None or upper.known.get(x) in (None, 'UNKNOWN'))):
                        slow[x] = slow.get(x, 0) + 1
            if slow:
                pick = sorted(slow, key=lambda x: (-slow[x], len(x[1])))[:long_max]
                retried.update(pick)
                if upper is not None:
                    # the larger ball refutes these much faster (measured: 30-40 s at radius four
                    # against 205 s at radius three for a window of the 9/2 cycle)
                    for x in pick:
                        upper.known.pop(x, None)
                    n = upper.query(pick, workers, long_timeout, verbose=False)
                    for x in pick:
                        if upper.known.get(x) == 'UNSAT':
                            oracle.known[x] = 'UNSAT'
                else:
                    for x in pick:
                        oracle.known.pop(x, None)
                    n = oracle.query(pick, workers, long_timeout, verbose=False)
                asked += n
                print(f'  greedy: retried {len(pick)} timed-out windows with {long_timeout:.0f} s: '
                      f'{sum(oracle.status(x) == "UNSAT" for x in pick)} refuted', flush=True)
                continue
        if not count:
            print(f'  greedy: {asked} queries, {len(alive)} of {len(cyc_wins)} cycles locally feasible', flush=True)
            return asked
        pick = sorted(count, key=lambda x: (-count[x], len(x[1])))[:chunk]
        asked += oracle.query(pick, workers, timeout, verbose=False)


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
    ap.add_argument('--long-timeout', type=float, default=None,
                    help='retry windows killed at --query-timeout with this limit when they are all that '
                         'could still break a cycle (each window once)')
    ap.add_argument('--start', action='store_true',
                    help='with --index: also the start-state constant D = max(pi - Q * symbol sum) of the '
                         'smallest-D potential and the bound C = L*P - Q*(L-k) + D gives')
    ap.add_argument('--cycle-budget', type=float, default=120.0,
                    help='seconds per round for extracting extra cycles (C Howard, delete-and-resolve)')
    ap.add_argument('--python-howard', action='store_true', help='use the pure-Python Howard (slow, one policy graph)')
    ap.add_argument('--escalate', type=int, default=None,
                    help='decide windows feasible at --radius again at this larger radius (two-level oracle)')
    ap.add_argument('--hybrid', action='store_true',
                    help='query every window of every extracted cycle at the base radius, then break the cycles '
                         'still unbroken greedily with the escalated radius (needs --escalate)')
    ap.add_argument('--greedy', action='store_true',
                    help='query only until every extracted cycle has an excluded window: windows shared by the most '
                         'unbroken cycles first, in parallel chunks')
    ap.add_argument('--lean', action='store_true',
                    help='LeanAutomaton: int32/uint8/int16 CSR edge arrays (~12 B/edge), chunked prune, '
                         'C Howard in place on the CSR (lean_automaton.py)')
    ap.add_argument('--final-max-edges', type=int, default=60_000_000,
                    help='with --lean: skip the final int64 Bellman-Ford / vertex bound above this many edges')
    ap.add_argument('--incremental', action='store_true',
                    help='with --lean: build the edge arrays once; later rounds only clear the edges of windows '
                         'refuted since (fastround.IncrementalLean) and re-prune in place; the Howard graph and '
                         'its policy are kept across rounds')
    ap.add_argument('--rc-cycles', action='store_true',
                    help='with --lean: extract the extra cycles by delete-and-resolve on the subgraph of edges with '
                         'Howard reduced cost <= --rc-R (doubling up to 4 when exhausted), not on the whole graph '
                         '(fastround.rc_cycles); same --batch / --slack / --cycle-budget')
    ap.add_argument('--rc-R', type=float, default=0.5, help='initial reduced-cost bound for --rc-cycles')
    a = ap.parse_args()
    if a.lean:
        assert not a.python_howard, '--lean needs the C Howard'
        from lean_automaton import LeanAutomaton, prune_lean, LeanHowardGraph, IdentityIndex
        from fastround import IncrementalLean, unsat_keys, rc_cycles
    assert a.lean or not (a.incremental or a.rc_cycles), '--incremental / --rc-cycles need --lean'
    if a.index:
        cases = [c for c in json.load(open(a.index))['cases'] if c['drat_trim_verified']]
        keys = [(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha'])) for c in cases]
        class Listed:
            known = {kk: 'UNSAT' for kk in keys}
            def status(self, kk): return self.known.get(kk)
        A = FastAutomaton(a.L, a.k, a.K)
        U, V, W, EXT = A.edges(Listed())
        m = prune(A.n, U, V); idx = np.nonzero(m)[0]
        from howard_fast import min_cycle
        mu, cyc = min_cycle(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
        lam = Fr(int(W[cyc].sum()), len(cyc))
        pi = bellman_ford(A.n, U, V, W, lam.numerator, lam.denominator)
        assert pi is not None
        slack = lam.denominator * W - lam.numerator + pi[U] - pi[V]
        assert (slack >= 0).all()
        vb = vertex_bound(A, U, V, W)
        out = {'L': a.L, 'k': a.k, 'K': a.K, 'listed_exclusions': len(keys), 'states': A.n, 'edges': int(len(U)),
               'min_mean': str(lam), 'potential_checked_on_every_edge': True,
               'potential_range': int(pi.max() - pi.min()), 'max_vertices': vb, 'max_edges': vb - 1}
        P, Q = lam.numerator, lam.denominator
        out['potential_bound_edges'] = (9179 * Q + P * a.L - Q * (a.L - 1) + out['potential_range'] - 8 * Q) // (P + 35 * Q)
        if a.start:
            from min_range import min_start_potential, init_sums
            D, pi2 = min_start_potential(A, U, V, W, P, Q, 300)
            assert pi2 is not None
            init = init_sums(A)
            assert (pi2 >= 0).all() and (pi2 <= D + Q * init).all()
            assert (Q * W - P + pi2[U] - pi2[V] >= 0).all()
            C = P * a.L - Q * (a.L - a.k) + D
            out.update({'start_constant_D': int(D), 'start_potential_range': int(pi2.max()),
                        'start_potential_checked_on_every_edge': True,
                        'start_potential_bound_edges': (9179 * Q + C - 8 * Q) // (P + 35 * Q)})
        print(json.dumps(out))
        if a.out:
            json.dump(out, open(a.out, 'w'), indent=1)
        return
    if a.escalate:
        from refine import TwoLevelOracle
        oracle = TwoLevelOracle(a.radius, a.escalate)
    else:
        oracle = Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            oracle.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    A = (LeanAutomaton if a.lean else FastAutomaton)(a.L, a.k, a.K)
    print('shapes', len(A.shapes), 'states', A.n, 'extensions', len(A.ext), flush=True)
    log = []
    prefer = None
    inc = G = None
    for rnd in range(a.rounds):
        t = time.time(); ph = {}
        if a.lean:
            upd = inc.update(oracle) if inc is not None else None
            if upd is None:
                U = V = W = EXT = m = G = inc = None    # free last round's graph before building the next
                U, V, W, EXT = A.edges(oracle)
                m = prune_lean(A.n, A.starts, V)
                if a.incremental:                       # m is updated in place; G.alive shares its buffer
                    inc = IncrementalLean(A, U, V, W, EXT, m, unsat_keys(oracle))
            else:
                print(f'  incremental: {upd[0]} new exclusions block {len(upd[1])} edges', flush=True)
            idx = IdentityIndex(m.sum())                # the lean Howard keeps the full edge numbering
        else:
            U, V, W, EXT = A.edges(oracle)
            m = prune(A.n, U, V)
            idx = np.nonzero(m)[0]
        ph['graph'] = time.time() - t
        if a.python_howard:
            mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
            batch = [c for m_, c in howard.extra if m_ <= mu + a.slack][:a.batch]
        else:
            # C Howard, warm-started from the previous round's policy; then many near-minimal
            # cycles by deleting each found cycle's edges and re-solving
            from howard_fast import HowardGraph
            if a.lean:
                if G is None or inc is None:            # incremental: same arrays, keep G and its policy
                    G = LeanHowardGraph(A.n, A.starts, V, W, m, prefer=prefer)
            else:
                G = HowardGraph(A.n, U[idx], V[idx], W[idx], prefer=prefer)
            mu, cyc = G.solve()
            prefer = G.successors()
            ph['howard'] = time.time() - t - ph['graph']
            if a.rc_cycles:
                batch = [c for m_, c in rc_cycles(G, a.batch, mu + a.slack, R=a.rc_R, budget=a.cycle_budget,
                                                  exclude=cyc, verbose=True)]
            else:
                batch = [c for m_, c in G.cycles(a.batch + 1, mu + a.slack, budget=a.cycle_budget)[1:]]
            ph['cycles'] = time.time() - t - ph['graph'] - ph['howard']
        t1 = time.time()
        cyc = [idx[e] for e in cyc]
        exact = Fr(int(W[cyc].sum()), len(cyc))
        wins = []
        cyc_wins = []
        for cyc2 in [cyc] + batch:
            cw = []
            for e in cyc2:
                e = idx[e] if cyc2 is not cyc else e
                ds, al = A.decode(U[e], EXT[e], W[e])
                for cc in range(2, a.k + 1):
                    cw.append(A.window_key(tuple(ds[-(cc + 1):]), tuple(al[-cc:])))
            cyc_wins.append(set(cw))
            wins.extend(cw)
        wins = list(dict.fromkeys(wins))
        ph['decode'] = time.time() - t1; t2 = time.time()
        if a.hybrid:
            newq = oracle.query(wins, a.workers, a.query_timeout, escalate=False)
            newq += greedy_break(oracle, cyc_wins, a.workers, a.query_timeout, long_timeout=a.long_timeout)
        elif a.greedy:
            newq = greedy_break(oracle, cyc_wins, a.workers, a.query_timeout, long_timeout=a.long_timeout)
        else:
            newq = oracle.query(wins, a.workers, a.query_timeout)
        ph['query'] = time.time() - t2
        unsat = [x for x in wins if oracle.status(x) == 'UNSAT']
        print(f'round {rnd}: edges {len(idx)} mean {exact} ({mu:.4f}) cycle {[int(x) for x in W[cyc]]} '
              f'extra-cycles {len(batch)} queried {newq} unsat-on-cycle {len(unsat)} [{time.time()-t:.0f}s: '
              + ' '.join(f'{k} {v:.0f}' for k, v in ph.items()) + ']', flush=True)
        log.append({'round': rnd, 'mean': str(exact), 'cycle_counts': [int(x) for x in W[cyc]],
                    'queried': newq, 'killed': len(unsat)})
        if not unsat:
            break
    final_counts = [int(x) for x in W[cyc]]
    n_edges = len(V)
    if inc is not None:
        # the arrays still hold edges blocked since the build: rebuild the last round's graph (same exclusions)
        class Built:
            known = {kk: 'UNSAT' for kk in inc.built}
            def status(self, kk): return self.known.get(kk)
        n_edges, _ = A.edges(Built(), count_only=True)
        G = m = inc = None
        if n_edges <= a.final_max_edges:
            U = V = W = EXT = None
            U, V, W, EXT = A.edges(Built())
    skipped = a.lean and n_edges > a.final_max_edges
    if skipped:
        pi = vb = None                                  # int64 Bellman-Ford needs ~45 B/edge: not at this size
    else:
        if a.lean:
            G = m = None; U = U.astype(np.int64); W = W.astype(np.int64)   # uint8 W wraps in q*W - p
        pi = bellman_ford(A.n, U, V, W, exact.numerator, exact.denominator)
        vb = vertex_bound(A, U, V, W)
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(exact),
           'exact_potential_found': None if skipped else pi is not None,
           'potential_range': int(pi.max() - pi.min()) if pi is not None else None,
           'max_vertices': vb, 'max_edges': vb - 1 if vb is not None else None, 'edges': int(n_edges),
           'final_cycle_counts': final_counts, 'rounds': log}
    json.dump(out, open(os.path.join(DATA, f'refine_L{a.L}_k{a.k}_K{a.K}_r{a.radius}.json'), 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'rounds'}))


if __name__ == '__main__':
    main()
