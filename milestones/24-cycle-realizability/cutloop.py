"""Forbid unrealizable periodic shape runs in the k6 full product and recompute the bound.

The base graph is the full product of gen_lean_automaton6.py (34 shapes x 6^5 counts),
built with the share_bonus/fp.py machinery from
  keys235   full_product/keys_235.json (1,287 keys), or
  allknown  every known plain-UNSAT lumped key (28,615; share_bonus/refine_share.status()).
A pattern is a cyclic shape walk C (minimal period p) with L_max(phase) from unroll.c: no
snake stays more than L_max(phase) consecutive transitions on C after entering it at
`phase`.  The product with a run-tracking DFA forbids every longer run:
  DFA state = set of active runs (k, start phase, length); a transition a -> b of shapes
  extends each run that expects it, kills the walk if a run exceeds L_max(start), and opens
  a run (k, phase, 1) wherever C_k has the transition a -> b at that phase (unless a run of
  C_k is already at that position: an earlier start dominates, since a suffix of a
  realizable run is realizable).
Each round: exact minimum cycle mean of the count weights (Lawler: BF with predecessor
cycles, then exact BF at the cycle mean), its cycle, the cycle's shape walk, and L_max of
that walk (exhaustive DFS, node limit).  If L_max is finite and the walk is not yet cut, it
becomes a new pattern.

  nice -n 10 python cutloop.py keys235 [rounds] [nodelimit]
"""
import sys, os, json, time
from fractions import Fraction as Fr
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'share_bonus'))
sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'full_product'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
sys.dont_write_bytecode = True
from shapes import unroll, minimal_period, canon  # noqa: E402

NC = 6 ** 5


def rss_mb():
    for l in open('/proc/self/status'):
        if l.startswith('VmRSS'):
            return int(l.split()[1]) / 1024


def base_graph(which):
    import bonus as BO
    import fp as FP
    if which == 'keys235':
        keys = BO.load_keys(os.path.join(MS, '23-k6-lean', 'full_product', 'keys_235.json'))
        Pr = FP.Product()
        for k in keys:
            Pr.apply(k)
        nkeys = len(keys)
    else:
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            'refine_share_k6', os.path.join(MS, '23-k6-lean', 'share_bonus', 'refine_share.py'))
        RS = importlib.util.module_from_spec(spec); spec.loader.exec_module(RS)
        S = RS.status(); Pr = FP.Product(); FP.load_all(S, Pr)
        nkeys = len(S.unsat())
    g = np.flatnonzero((Pr.CNT == 0).ravel())
    u, v, s = Pr.uvw(g)
    shp = [tuple(c) for c in Pr.shp]
    del Pr
    return shp, u.astype(np.int64), v.astype(np.int64), s.astype(np.int64), nkeys


class DFA:
    def __init__(self, pats):
        self.pats = pats                       # [(states tuple of 7-shapes, Lmax list)]

    def step(self, q, a, b):
        new = set()
        for (k, f0, ln) in q:
            C, L = self.pats[k]; p = len(C)
            pos = (f0 + ln) % p
            if C[pos] == a and C[(pos + 1) % p] == b:
                if ln + 1 > L[f0]:
                    return None
                new.add((k, f0, ln + 1))
        at = {(k, (f0 + ln) % len(self.pats[k][0])) for (k, f0, ln) in new}
        for k, (C, L) in enumerate(self.pats):
            p = len(C)
            for f in range(p):
                if C[f] == a and C[(f + 1) % p] == b and (k, (f + 1) % p) not in at:
                    if 1 > L[f]:
                        return None
                    new.add((k, f, 1))
        return frozenset(new)


def product(shp, u, v, s, pats):
    """Product of the base graph with the run DFA.  Returns (n, U, V, S, node_shape, node_q)."""
    sid = {c: i for i, c in enumerate(shp)}
    su, sv = u // NC, v // NC
    pair = su * 64 + sv
    order = np.argsort(pair, kind='stable')
    pairs, starts = np.unique(pair[order], return_index=True)
    ends = list(starts[1:]) + [len(order)]
    succ = {}
    for pr in pairs:
        succ.setdefault(int(pr) // 64, []).append(int(pr) % 64)
    dfa = DFA(pats)
    # reachable (shape, q) pairs, from every shape with no active run
    ids = {}
    stack = []
    for a in range(len(shp)):
        ids[(a, frozenset())] = len(ids); stack.append((a, frozenset()))
    trans = {}
    while stack:
        a, q = stack.pop()
        for b in succ.get(a, []):
            q2 = dfa.step(q, shp[a], shp[b])
            trans[(a, q, b)] = q2
            if q2 is not None and (b, q2) not in ids:
                ids[(b, q2)] = len(ids); stack.append((b, q2))
    byshape = {}
    for (a, q), i in ids.items():
        byshape.setdefault(a, []).append((q, i))
    U, V, S = [], [], []
    for pr, st, en in zip(pairs, starts, ends):
        a, b = int(pr) // 64, int(pr) % 64
        e = order[st:en]
        cu, cv = u[e] % NC, v[e] % NC
        for q, i in byshape[a]:
            q2 = trans[(a, q, b)]
            if q2 is None:
                continue
            j = ids[(b, q2)]
            U.append(i * NC + cu); V.append(j * NC + cv); S.append(s[e])
    n = len(ids) * NC
    node_shape = np.zeros(len(ids), np.int64)
    node_q = [None] * len(ids)
    for (a, q), i in ids.items():
        node_shape[i] = a; node_q[i] = q
    return n, np.concatenate(U), np.concatenate(V), np.concatenate(S), node_shape, node_q


def prune(n, U, V):
    alive = np.ones(n, bool)
    while True:
        m = alive[U] & alive[V]
        new = alive & (np.bincount(U[m], minlength=n) > 0)
        new &= np.bincount(V[m & new[U]], minlength=n) > 0
        if (new == alive).all():
            return m
        alive = new


class BF:
    def __init__(self, n, U, V, S):
        o = np.argsort(V, kind='stable')
        self.n = n
        self.U, self.V, self.S = U[o], V[o], S[o]
        self.uv, self.starts = np.unique(self.V, return_index=True)
        self.vidx = np.searchsorted(self.uv, self.V)

    def run(self, P, Q, maxit=3000, check_every=25):
        """BF from pi = 0 for weights Q s - P.  Returns ('ok', pi) or ('neg', cycle edge ids)."""
        W = Q * self.S - P
        pi = np.zeros(self.n, np.int64)
        pred = np.full(self.n, -1, np.int64)
        for it in range(maxit):
            cand = pi[self.U] + W
            mins = np.minimum.reduceat(cand, self.starts)
            upd = mins < pi[self.uv]
            if not upd.any():
                return 'ok', pi, it
            pi[self.uv[upd]] = mins[upd]
            # predecessor edge: an edge achieving the new minimum
            hit = np.flatnonzero(upd[self.vidx] & (cand == pi[self.V]))
            pred[self.V[hit]] = hit
            if it % check_every == check_every - 1:
                cyc = self.pred_cycle(pred, self.uv[upd][:200])
                if cyc is not None:
                    return 'neg', cyc, it
        raise RuntimeError('BF did not settle')

    def pred_cycle(self, pred, starts):
        for x0 in starts:
            seen = {}
            x = int(x0); seq = []
            while pred[x] >= 0 and x not in seen and len(seq) < 100000:
                seen[x] = len(seq); e = int(pred[x]); seq.append(e); x = int(self.U[e])
            if pred[x] >= 0 and x in seen:
                cyc = list(reversed(seq[seen[x]:]))
                return cyc
        return None


def mcm(bf, lam0=Fr(4)):
    """Exact minimum cycle mean (Lawler-style descent from lam0, which must be >= mcm or any
    value: we first go up if lam0 is feasible).  Returns (lam, cycle, pi, rounds)."""
    lam = lam0
    st, x, it = bf.run(lam.numerator, lam.denominator)
    if st == 'ok':
        # lam0 feasible: find a cycle with mean = mcm by raising lam until infeasible
        hi = lam + 1
        while True:
            st2, x2, _ = bf.run(hi.numerator, hi.denominator)
            if st2 == 'neg':
                cyc = x2; break
            hi += 1
    else:
        cyc = x
    while True:
        mu = Fr(int(sum(int(bf.S[e]) for e in cyc)), len(cyc))
        st, x, it = bf.run(mu.numerator, mu.denominator)
        if st == 'ok':
            return mu, cyc, x, it
        cyc = x


def bound(lam, rng):
    P, Q = lam.numerator, lam.denominator
    bits = max(1, int(rng).bit_length())
    return (9171 * Q + 7 * P + (2 ** bits - 1) - 6 * Q) // (P + 35 * Q), bits


def main():
    which = sys.argv[1]
    rounds = int(sys.argv[2]) if len(sys.argv) > 2 else 10
    limit = int(sys.argv[3]) if len(sys.argv) > 3 else 20_000_000
    # optimistic: when the DFS hits the node limit, cut at its LOWER bound on L_max anyway.
    # That forbids more than is true, so the resulting mean is an upper estimate (a ceiling)
    # of what exact cuts can give; it is not a valid bound.
    optimistic = len(sys.argv) > 4 and sys.argv[4] == 'optimistic'
    outp = os.path.join(HERE, 'data', f'cutloop_{which}{"_opt" if len(sys.argv) > 4 else ""}.json')
    t0 = time.time()
    shp, u, v, s, nkeys = base_graph(which)
    print(f'{which}: {nkeys} keys, {len(u)} base transitions, {time.time() - t0:.0f}s, rss {rss_mb():.0f} MB', flush=True)
    pats, log, exact = [], [], []
    lam_prev = Fr(4)
    for r in range(rounds):
        t1 = time.time()
        n, U, V, S, nsh, nq = product(shp, u, v, s, pats)
        m = prune(n, U, V)
        U, V, S = U[m], V[m], S[m]
        bf = BF(n, U, V, S)
        lam, cyc, pi, it = mcm(bf, lam_prev)
        live = np.zeros(n, bool); live[U] = True
        rng = int(pi[live].max() - pi[live].min())
        b, bits = bound(lam, rng)
        cu = [int(bf.U[e]) for e in cyc]
        cs = [shp[int(nsh[x // NC])] for x in cu]
        counts = [int(bf.S[e]) for e in cyc]
        q = minimal_period(cs)
        walk = cs[:q]
        res = [unroll(walk, ph, limit=limit) for ph in range(q)]
        L = [x['max_transitions'] for x in res]
        exh = all(x['exhaustive'] for x in res)
        rec = dict(round=r, patterns=len(pats), product_states=n, product_nodes_live=int(live.sum()),
                   transitions=int(len(U)), lam=str(lam), lam_float=float(lam), pot_range=rng,
                   bits=bits, bound=b, cycle_len=len(cyc), counts=counts, shape_period=q,
                   shapes=[''.join(map(str, c)) for c in walk], L_max=L, exhaustive=exh,
                   seconds=round(time.time() - t1), rss_mb=round(rss_mb()))
        print(json.dumps(rec), flush=True)
        log.append(rec)
        json.dump(dict(which=which, nkeys=nkeys, rounds=log,
                       patterns=[dict(states=[''.join(map(str, c)) for c in C], L_max=Lm, exact=ex) for (C, Lm), ex in zip(pats, exact)]),
                  open(outp, 'w'), indent=1)
        lam_prev = lam
        key = tuple(walk)
        if not exh and not optimistic:
            print('L_max not determined exhaustively: stop', flush=True); break
        if any(set(map(tuple, C)) == set(key) and len(C) == q for C, _ in pats):
            print('cycle already a pattern (should not happen): stop', flush=True); break
        pats.append((key, L)); exact.append(exh)


if __name__ == '__main__':
    main()
