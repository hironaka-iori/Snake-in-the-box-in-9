"""Solver-side feasibility probe for the bound 233 on the k7 automaton (milestone 25).

Bound (k7, milestone 25):  (P + 35 Q) m + 7 Q <= 9171 Q + 8 P + 2^B - 1.
  m = 234 is excluded iff 234 (P + 35 Q) + 7 Q > 9171 Q + 8 P + 2^B - 1, i.e.
      226 P - 974 Q >= 2^B,   potential range <= 2^B - 1.
  So 233 needs lambda = P/Q > 974/226 = 487/113 = 4.30973 and a range sigma (count units)
  < 226 lambda - 974.

Product: k7.K7 with every known exclusion (prune234.pool: k6_loop, k6_w3, k6_w3_loop,
oracle_full, share_bonus, decide234 k6 keys; every UNSAT F8/H9 key of oracle_k7, oracle234,
decide234) plus the decisions of this probe (data/oracle233.jsonl.gz).

Minimum cycle mean: Howard's policy iteration on the structured product (predecessor form:
every node picks one in-edge; the weight of u -> v is the new count of v).  The tight
subgraph (reduced cost 0 at the minimum mean) is cut by deciding the windows of its edges:
  H9  (9 dirs, counts a2..a8, a1 free)  -- every edge,
  F8  (dirs 2..9, counts a2..a8)         -- generalisation of an UNSAT H9 (--gen f8|k6),
  k6  (7 dirs, counts a3..a8; 6 dirs, counts a4..a8) -- generalisation (--gen k6).
A round that cuts nothing leaves a minimum-mean cycle all of whose windows are SAT: the
ceiling of the k7 automaton with windows of at most 9 directions at radius 4.

  nice -n 19 python probe233.py mcm
  nice -n 19 python probe233.py loop --hours H [--maxtest N] [--gen h9|f8|k6]
  nice -n 19 python probe233.py rigor --lams 4.17 4.2 ...   (BF from 0 at P/Q: range, bound)
  nice -n 19 python probe233.py ceiling                      (H10 / radius 5 on the ceiling cycle)
"""
import sys, os, json, time, gzip, random
sys.dont_write_bytecode = True
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '25-k7-234'))
import numpy as np
from fractions import Fraction as Fr
import k7                     # noqa: E402
import prune234 as P4         # noqa: E402
from k7 import NC, NT, N7, cidx, digits, canon, W, LUMP   # noqa: E402
from pysat.solvers import Cadical153   # noqa: E402

D = os.path.join(HERE, 'data')
ORACLE = os.path.join(D, 'oracle233.jsonl.gz')
ROUNDS = os.path.join(D, 'rounds233.jsonl')
LAM233 = Fr(974, 226)
BUDGET = int(os.environ.get('BUDGET', 1_000_000))      # CaDiCaL conflicts per solve call
GEN_BUDGET = 60_000                                     # for optional generalisations


def bound(P, Q, B):
    return k7.bound(P, Q, B)


def need233(P, Q):
    """Largest allowed range 2^B - 1 for 233 at P/Q (None if lambda <= 974/226)."""
    g = 226 * P - 974 * Q
    if g < 1:
        return None
    B = g.bit_length() - 1
    assert bound(P, Q, B) <= 233
    return B


def best_pq233(lam, qmax=4000):
    best = None
    for Q in range(1, qmax + 1):
        P = int(lam * Q)
        B = need233(P, Q)
        if B is None:
            continue
        sl = (2 ** B - 1) / Q
        if best is None or sl > best[3] + 1e-12:
            best = (P, Q, B, sl)
    return best


def guard():
    k7.guard()


# ------------------------------------------------------------------ decisions
def enc_of(kind, ds, syms, radius=4):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    al = [LUMP[s] for s in syms] + ([None] if kind in ('H', 'H10') else [])
    return W.Encoding(vs, al, radius)


def solve(enc, budget=BUDGET, tlim=60.0):
    """Lazy cycle-cut solve with a conflict budget per call and a wall-clock limit overall."""
    cuts = 0
    t0 = time.time()
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while True:
            s.conf_budget(budget)
            r = s.solve_limited()
            if r is None:
                return 'TIMEOUT', cuts
            if not r:
                return 'UNSAT', cuts
            if time.time() - t0 > tlim:
                return 'TIMEOUT', cuts
            model = s.get_model()
            sel = [v for v in enc.ball if model[enc.var[v] - 1] > 0]
            cyc = W.cycles_of(sel)
            if not cyc:
                return 'SAT', cuts
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
                s.add_clause(enc.clauses[-1])


class Oracle(P4.Oracle):
    """oracle_k7 + oracle234 + decide234 (read) and oracle233 (read/write).  Keys of this
    file carry a radius: (kind, dirs, syms, radius); radius-4 F/H/k6 keys are also stored
    under the 3-tuple form used by k7."""
    def __init__(self, S):
        super().__init__()
        self.S = S
        self.r = {}
        self.vars = {}
        if os.path.exists(ORACLE):
            for l in gzip.open(ORACLE, 'rt'):
                r = json.loads(l)
                self._put(r)
        self.buf = []
        self.ndec = 0; self.tdec = 0.0

    def _put(self, r):
        k = (r['kind'], tuple(r['dirs']), tuple(r['syms']))
        rad = r.get('radius', 4)
        self.r[k + (rad,)] = r['result']
        self.sec[k + (rad,)] = r['seconds']
        if rad == 4:
            if r['kind'] == 'k6':
                if self.S.st.get((k[1], k[2])) in (None, 'TIMEOUT'):
                    self.S.st[(k[1], k[2])] = r['result']
            else:
                self.st[k] = r['result']; self.sec[k] = r['seconds']

    def status(self, k, radius=4):
        if radius == 4:
            if k[0] == 'k6':
                return self.S.st.get((k[1], k[2]))
            if k in self.st:
                return self.st[k]
        return self.r.get(k + (radius,))

    def get(self, k, radius=4, budget=BUDGET, tlim=60.0):
        st = self.status(k, radius)
        if st is not None and st != 'TIMEOUT':
            return st
        if st == 'TIMEOUT':
            return st
        guard()
        enc = enc_of(k[0], k[1], k[2], radius)
        t = time.time()
        st, cuts = solve(enc, budget, tlim)
        sec = time.time() - t
        self.ndec += 1; self.tdec += sec
        r = dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st, seconds=round(sec, 3), cuts=cuts,
                 nvars=enc.nv, ncls=len(enc.clauses))
        if radius != 4:
            r['radius'] = radius
        self._put(r)
        self.buf.append(r)
        if len(self.buf) >= 200:
            self.flush()
        return st

    def flush(self):
        if self.buf:
            st = os.statvfs('/')
            if st.f_bavail * st.f_frsize / 2 ** 20 < 400:
                print('disk under 400 MB: not writing', flush=True)
                return
            with gzip.open(ORACLE, 'at') as f:
                for r in self.buf:
                    f.write(json.dumps(r, separators=(',', ':')) + '\n')
            self.buf = []


def mine_unsat():
    """k6 and F/H keys found UNSAT by this probe (radius 4)."""
    k6, new = [], []
    if os.path.exists(ORACLE):
        for l in gzip.open(ORACLE, 'rt'):
            r = json.loads(l)
            if r.get('radius', 4) != 4 or r['result'] != 'UNSAT':
                continue
            if r['kind'] == 'k6':
                k6.append((tuple(r['dirs']), tuple(r['syms'])))
            elif r['kind'] in ('H', 'F'):
                new.append((r['kind'], tuple(r['dirs']), tuple(r['syms'])))
    return k6, new


def build():
    t0 = time.time()
    S, O0, keys6, newk = P4.pool()
    O = Oracle(S)
    m6, mn = mine_unsat()
    keys6 = sorted(set(keys6) | set(m6))
    newk = sorted(set(newk) | set(mn))
    K = k7.K7(S, keys6)
    for k in newk:
        K.add_new(k)
    print(f'build: {len(keys6)} k6 keys, {len(newk)} F8/H9 keys, {int(K.alive.sum())} live states, '
          f'{time.time() - t0:.0f}s, rss {k7.rss_mb():.0f} MB', flush=True)
    return S, O, K


def add_k6(K, k):
    if k in K._k6set:
        return
    K._k6set.add(k)
    K.Pr.apply(k)


# ------------------------------------------------------------------ Howard
class Howard:
    """Minimum cycle mean of the count of the target, structured product.
    Policy p[v] = X*6 + t0 (an in-edge of v), -1 if none."""
    def __init__(self, K):
        self.K = K
        self.N = K.nE * NT
        self.c = (np.arange(self.N) % 6 + 1).astype(np.float64)
        self.p = np.full(self.N, -1, np.int32)
        self.Xs = np.array([e for e, _ in K.XE], np.int64)
        self.refresh()

    def refresh(self):
        K = self.K
        K.alive = (K.Pr.CNT == 0)
        self.M = [K.mask(i) for i in range(K.nX)]
        # in-core: drop states with no in-edge from the core (every core state then has a
        # predecessor in the core, so every policy chain ends in a cycle)
        live = K.alive.copy()
        if getattr(self, 'core', None) is not None:
            live &= self.core
        for _ in range(100000):
            hasin = np.zeros_like(live)
            for i, (e, e2) in enumerate(K.XE):
                h = hasin[e2].reshape(NC, 6)
                h |= (self.M[i] & live[e].reshape(6, NC, 1)).any(0)
            new = live & hasin
            if new.sum() == live.sum():
                break
            live = new
        self.core = live
        for i, (e, e2) in enumerate(K.XE):
            self.M[i] &= live[e].reshape(6, NC, 1) & live[e2].reshape(1, NC, 6)
        # drop policy edges that are no longer allowed
        p = self.p
        for i, (e, e2) in enumerate(K.XE):
            sl = p[e2 * NT:(e2 + 1) * NT].reshape(NC, 6)
            sel = (sl >= 0) & (sl // 6 == i)
            if not sel.any():
                continue
            t0 = np.where(sel, sl % 6, 0)
            ok = np.take_along_axis(self.M[i], t0[None], 0)[0]
            bad = sel & ~ok
            sl[bad] = -1
        p[~live.ravel()] = -1

    def src(self):
        v = np.arange(self.N, dtype=np.int64)
        f = v.copy()
        ok = self.p >= 0
        pp = self.p[ok].astype(np.int64)
        f[ok] = self.Xs[pp // 6] * NT + (pp % 6) * NC + (v[ok] % NT) // 6
        return f

    def evaluate(self):
        """Policy evaluation on the core nodes (compressed, int32), with early-stopped
        pointer doubling: J = f^(2^k) until f permutes the image of J (= the cycle nodes)."""
        N = self.N
        f = self.src()
        cidx_ = np.flatnonzero(self.core.ravel())
        n = len(cidx_)
        pm = np.full(N, -1, np.int64); pm[cidx_] = np.arange(n)
        fc = pm[f[cidx_]]
        assert (fc >= 0).all()
        fc = fc.astype(np.int32)
        root = self.p[cidx_] < 0
        cc = self.c[cidx_]
        J = fc.copy()
        for k in range(40):
            J = J[J]
            if k >= 3:
                S = np.zeros(n, bool); S[J] = True; S &= ~root
                idx = np.flatnonzero(S)
                fi = fc[idx]
                if S[fi].all() and len(np.unique(fi)) == len(idx):
                    break
        onc = np.zeros(n, bool); onc[J] = True; onc &= ~root
        C = np.flatnonzero(onc)
        g = np.searchsorted(C, fc[C])
        m = np.arange(len(C)); F = g.copy(); k = 1
        while k < len(C):
            m = np.minimum(m, m[F]); F = F[F]; k *= 2
        lens = np.bincount(m, minlength=len(C)).astype(np.float64)
        sums = np.bincount(m, weights=cc[C], minlength=len(C))
        mean = np.where(lens > 0, sums / np.maximum(lens, 1), np.inf)
        eta = np.full(n, np.inf)
        inC = onc[J]
        pos = np.searchsorted(C, J[inC])
        eta[inC] = mean[m[pos]]
        isrep = np.zeros(n, bool); isrep[C[m == np.arange(len(C))]] = True
        F = fc.copy(); F[isrep] = np.flatnonzero(isrep)
        fin = np.isfinite(eta)
        Dv = np.where(isrep | ~fin, 0.0, cc - np.where(fin, eta, 0.0))
        for _ in range(40):
            F2 = F[F]
            if np.array_equal(F2, F):
                break
            Dv = Dv + Dv[F]; F = F2
        self.eta = np.full(N, np.inf); self.eta[cidx_] = eta
        self.d = np.zeros(N); self.d[cidx_] = Dv
        self.C, self.m, self.f = cidx_[C], m, f
        self.Jfull = cidx_[J]
        self.ncore = n
        self.ncyc = int((lens > 0).sum())
        return self.eta, self.d

    def improve(self, eps=1e-9, deps=1e-7):
        K, N = self.K, self.N
        eta, d = self.eta, self.d
        minEta = np.full(N, np.inf)
        for i, (e, e2) in enumerate(K.XE):
            es = eta[e * NT:(e + 1) * NT].reshape(6, NC, 1)
            cand = np.where(self.M[i], es, np.inf).min(0)
            tgt = minEta[e2 * NT:(e2 + 1) * NT].reshape(NC, 6)
            np.minimum(tgt, cand, out=tgt)
        bestD = np.full(N, np.inf); bestP = np.full(N, -1, np.int32)
        for i, (e, e2) in enumerate(K.XE):
            es = eta[e * NT:(e + 1) * NT].reshape(6, NC, 1)
            tm = minEta[e2 * NT:(e2 + 1) * NT].reshape(1, NC, 6)
            ok = self.M[i] & (es <= tm + eps)
            if not ok.any():
                continue
            dd = np.where(ok, d[e * NT:(e + 1) * NT].reshape(6, NC, 1), np.inf)
            am = dd.argmin(0)
            mn = np.take_along_axis(dd, am[None], 0)[0]
            tb = bestD[e2 * NT:(e2 + 1) * NT].reshape(NC, 6)
            upd = mn < tb
            if upd.any():
                tb[upd] = mn[upd]
                bestP[e2 * NT:(e2 + 1) * NT].reshape(NC, 6)[upd] = (i * 6 + am[upd]).astype(np.int32)
        has = bestP >= 0
        with np.errstate(invalid='ignore'):
            sw_eta = has & (minEta < eta - eps)
            sw_d = has & ~sw_eta & (np.abs(minEta - eta) <= eps) & (bestD + self.c - eta < d - deps)
        sw = sw_eta | sw_d | ((self.p < 0) & has)
        self.p[sw] = bestP[sw]
        return int(sw.sum()), int(sw_eta.sum())

    def run(self, maxit=200, verbose=True):
        t0 = time.time()
        for it in range(maxit):
            self.evaluate()
            n, ne = self.improve()
            if verbose:
                fin = np.isfinite(self.eta)
                me = float(self.eta[fin].min()) if fin.any() else float('inf')
                print(f'  howard {it}: min eta {me:.6f}, '
                      f'cycles {self.ncyc}, switches {n} ({ne} by eta), {time.time() - t0:.0f}s', flush=True)
            if n == 0:
                return it
        return maxit

    def min_cycle(self):
        """Exact (mean, transitions) of a policy cycle of minimum mean: list of (X, c a2..a8)."""
        fin = np.isfinite(self.eta)
        v0 = int(np.flatnonzero(fin)[np.argmin(self.eta[fin])])
        f = self.f
        v = int(self.C[self.m[np.searchsorted(self.C, self.Jfull[v0])]])     # the cycle's rep
        start, cyc = v, []
        while True:
            cyc.append(v); v = int(f[v])
            if v == start:
                break
        tr = []
        for v in cyc:                    # v's in-edge
            p = int(self.p[v]); i, t0 = divmod(p, 6)
            x = v % NT
            tr.append((i, (t0 + 1,) + digits(x, 6)))
        tr = tr[::-1]                    # forward order
        mean = Fr(sum(c[-1] for _, c in tr), len(tr))
        return mean, tr

    def tight(self, lam, delta=0.0, R=0.0, tol=1e-7, eps=1e-9):
        """Near-critical edges (X, flat 7-count index): eta(u) = eta(v) <= lam + delta and
        reduced cost d(u) + s - eta - d(v) <= R, restricted to the cyclic core of that
        subgraph; sorted by (eta, reduced cost).  delta = R = 0 gives the edges of the
        minimum-mean cycles.  A cycle of length l and mean eta + r lies in it when l r <= R."""
        K = self.K
        eta, d = self.eta, self.d
        I, Fl, U, V, Key = [], [], [], [], []
        top = lam + delta + eps
        for i, (e, e2) in enumerate(K.XE):
            es = eta[e * NT:(e + 1) * NT].reshape(6, NC, 1)
            et = eta[e2 * NT:(e2 + 1) * NT].reshape(1, NC, 6)
            ok = self.M[i] & (es <= top) & (np.abs(es - et) <= eps)
            if not ok.any():
                continue
            rc = d[e * NT:(e + 1) * NT].reshape(6, NC, 1) + np.arange(1, 7).reshape(1, 1, 6) - es \
                - d[e2 * NT:(e2 + 1) * NT].reshape(1, NC, 6)
            ok &= rc <= R + tol
            fl = np.flatnonzero(ok)
            if len(fl) == 0:
                continue
            I.append(np.full(len(fl), i, np.int32)); Fl.append(fl)
            U.append(e * NT + fl // 6); V.append(e2 * NT + fl % NT)
            Key.append(np.broadcast_to(es, ok.shape).ravel()[fl] * 1e3 + rc.ravel()[fl])
        if not I:
            return np.zeros(0, np.int32), np.zeros(0, np.int64)
        I = np.concatenate(I); Fl = np.concatenate(Fl); U = np.concatenate(U); V = np.concatenate(V)
        Key = np.concatenate(Key)
        keep = np.ones(len(I), bool)
        while True:                       # cyclic core
            hasin = np.zeros(self.N, bool); hasin[V[keep]] = True
            hasout = np.zeros(self.N, bool); hasout[U[keep]] = True
            k2 = keep & hasin[U] & hasout[V]
            if k2.sum() == keep.sum():
                break
            keep = k2
        o = np.flatnonzero(keep)
        o = o[np.argsort(Key[o], kind='stable')]
        return I[o], Fl[o]


# ------------------------------------------------------------------ windows of a transition
def windows(K, i, c, gen):
    """Generalisations of the H9 window of transition (X, c), most specific first:
    F8 (dirs 2..9, counts a2..a8), k6 (7 dirs, a3..a8), k6 (6 dirs, a4..a8).  Each one's
    clause set is contained in the previous one's, so UNSAT of one implies UNSAT of those before."""
    X = K.X[i]
    out = []
    if gen in ('k6', 'k6x', 'f8'):
        out.append(k7.f8_key(X, c))
    if gen in ('k6', 'k6x'):
        out.append(('k6',) + k7.FP.lkey(X[2:], c[1:]))
    if gen == 'k6x':
        out.append(('k6',) + k7.FP.lkey(X[3:], c[2:]))
    return out


def allowed(K, i, c):
    e, e2 = K.XE[i]
    return bool(K.alive[e, cidx(c[:6])] and K.alive[e2, cidx(c[1:])] and K.newcnt[i, cidx(c)] == 0)


def cut_edge(K, O, i, c, gen, stats):
    """Decide the H9 window of (X, c); if UNSAT, walk up the generalisations while they stay
    UNSAT and apply the most general UNSAT key.  Returns True if the transition is cut."""
    h = k7.h9_key(K.X[i], c)
    st = O.get(h)
    stats[('H', st)] = stats.get(('H', st), 0) + 1
    if st != 'UNSAT':
        return False
    best = h
    for k in windows(K, i, c, gen):
        s2 = O.get(k, budget=GEN_BUDGET, tlim=3.0)
        stats[(k[0], s2)] = stats.get((k[0], s2), 0) + 1
        if s2 != 'UNSAT':
            break
        best = k
    if best[0] == 'k6':
        add_k6(K, (best[1], best[2]))
        K.alive = (K.Pr.CNT == 0)
    else:
        K.add_new(best)
    return True


def log_round(rec):
    with open(ROUNDS, 'a') as f:
        f.write(json.dumps(rec, separators=(',', ':')) + '\n')


def loop(hours, maxtest, gen, tag, delta=0.0, R=0.0):
    S, O, K = build()
    K._k6set = set()
    H = Howard(K)
    t0 = time.time()
    rnd = 0
    rng = random.Random(1)
    while True:
        guard()
        tr0 = time.time()
        it = H.run(verbose=False)
        lam, cyc = H.min_cycle()
        th = time.time() - tr0
        I, Fl = H.tight(float(lam), delta, R)
        nt = len(I)
        # policy cycle edges first, then the near-critical core by (eta, reduced cost)
        first = [(i, c) for i, c in cyc]
        rest = list(zip(I.tolist(), Fl.tolist()))
        seen = set(); order = []
        for i, c in first:
            key = (i, cidx(c))
            if key not in seen:
                seen.add(key); order.append((i, c))
        for i, fl in rest:
            if (i, fl) not in seen:
                seen.add((i, fl)); order.append((i, digits(fl, 7)))
        stats = {}
        cut = tested = 0
        cyc_cut = 0
        nd0, td0 = O.ndec, O.tdec
        for j, (i, c) in enumerate(order):
            if tested >= maxtest:
                break
            if not allowed(K, i, c):
                continue
            tested += 1
            if cut_edge(K, O, i, c, gen, stats):
                cut += 1
                if j < len(first):
                    cyc_cut += 1
        O.flush()
        rec = dict(tag=tag, round=rnd, time=time.strftime('%H:%M:%S'), lam=str(lam), lam_f=round(float(lam), 6),
                   core=H.ncore, delta=delta, R=R,
                   cycle_len=len(cyc), cycle_counts=[c[-1] for _, c in cyc], howard_it=it, howard_s=round(th),
                   tight_edges=nt, tested=tested, cut=cut, cycle_cut=cyc_cut,
                   decided_new=O.ndec - nd0, solve_s=round(O.tdec - td0), decided_total=O.ndec,
                   stats={f'{a}:{b}': v for (a, b), v in sorted(stats.items())},
                   new_keys=len(K.newkeys), new_k6=len(K._k6set), rss=round(k7.rss_mb()),
                   elapsed=round(time.time() - t0))
        # ceiling test: a cycle of exactly tight (minimum-mean) edges whose H9 windows are SAT
        Ti, Tf = H.tight(float(lam))
        sat = []
        for i, fl in zip(Ti.tolist(), Tf.tolist()):
            if O.status(k7.h9_key(K.X[i], digits(fl, 7))) == 'SAT':
                sat.append((i, fl))
        scyc = sat_cycle(K, sat)
        rec.update(tight0=int(len(Ti)), tight0_sat=len(sat))
        print(json.dumps(rec), flush=True)
        log_round(rec)
        if scyc or cut == 0:
            cc = scyc if scyc else cyc
            mean = Fr(sum(c[-1] for _, c in cc), len(cc))
            rec2 = dict(tag=tag, ceiling=True, lam=str(lam), mean=str(mean),
                        cycle=[[list(K.X[i]), list(c)] for i, c in cc])
            log_round(rec2)
            print('CEILING', json.dumps(rec2), flush=True)
            return K, H, O, lam, cc
        if time.time() - t0 > hours * 3600:
            log_round(dict(tag=tag, final=True, lam=str(lam), cycle=[[list(K.X[i]), list(c)] for i, c in cyc]))
            return K, H, O, lam, None
        H.refresh()
        rnd += 1


def sat_cycle(K, edges):
    """A cycle (list of (X, c), forward) in the subgraph of the given (X index, flat count)
    edges, or None."""
    if not edges:
        return None
    U = np.array([K.XE[i][0] * NT + fl // 6 for i, fl in edges], np.int64)
    V = np.array([K.XE[i][1] * NT + fl % NT for i, fl in edges], np.int64)
    keep = np.ones(len(edges), bool)
    while True:
        hin = set(V[keep].tolist()); hout = set(U[keep].tolist())
        k2 = keep & np.array([u in hin for u in U.tolist()]) & np.array([v in hout for v in V.tolist()])
        if k2.sum() == keep.sum():
            break
        keep = k2
    if not keep.any():
        return None
    out = {}
    for j in np.flatnonzero(keep):
        out.setdefault(int(U[j]), []).append(j)
    v = int(U[np.flatnonzero(keep)[0]]); path = []; pos = {}
    while v not in pos:
        pos[v] = len(path)
        j = out[v][0]; path.append(j); v = int(V[j])
    cyc = path[pos[v]:]
    return [(edges[j][0], digits(edges[j][1], 7)) for j in cyc]


def options10(X, c, X2, c2):
    """Concrete 10-direction windows of consecutive k7 transitions (X, c), (X2, c2), as H10
    keys (reversed, uncounted last): directions X ++ [d], counts a2..a9 = c ++ [c2[-1]].  A
    fresh label of X2 is concretely X[0] (when X[0] is not in X[1:]) or a brand-new
    coordinate.  Non-induced options are impossible and dropped.  The k8 state after X is X
    itself (9 directions), and both fresh options lead to the same next k8 shape X2, so the
    k7 cycle survives in k8 iff every pair has an option whose window is SAT."""
    tail = X[1:]
    assert tuple(X2[:8]) == canon(tail), (X, X2)
    order = []
    for x in tail:
        if x not in order:
            order.append(x)
    d = X2[-1]
    if d < len(order):
        opts = [tuple(X) + (order[d],)]
    else:
        opts = []
        if X[0] not in tail:
            opts.append(tuple(X) + (X[0],))
        fresh = [x for x in range(9) if x not in X]
        if fresh:
            opts.append(tuple(X) + (fresh[0],))
    cnt = tuple(c) + (c2[-1],)
    return [('H10', canon(tuple(reversed(ds))), tuple(reversed(cnt))) for ds in opts if k7.GA.induced(ds)]


def ceiling_test(O, cyc, radii10=(4, 5), r9=(5,)):
    """cyc: list of (X, c) (9 directions, counts a2..a8) of a k7 cycle.  Decides, per position:
    H9 at radius 4 (and r9), every concrete H10 option at the radii10."""
    rows = []
    n = len(cyc)
    for j in range(n):
        X, c = tuple(cyc[j][0]), tuple(cyc[j][1])
        X2, c2 = tuple(cyc[(j + 1) % n][0]), tuple(cyc[(j + 1) % n][1])
        h = ('H', canon(tuple(reversed(X))), tuple(reversed(c)))
        row = dict(j=j, X=list(X), c=list(c), h9_r4=O.get(h))
        for r in r9:
            t = time.time(); row[f'h9_r{r}'] = O.get(h, radius=r); row[f'h9_r{r}_s'] = round(time.time() - t, 2)
        opts = options10(X, c, X2, c2)
        row['h10_options'] = len(opts)
        for r in radii10:
            sts = []
            for k in opts:
                t = time.time(); sts.append(O.get(k, radius=r))
            row[f'h10_r{r}'] = sts
            row[f'h10_r{r}_dead'] = all(s == 'UNSAT' for s in sts)
        O.flush()
        print(json.dumps(row), flush=True)
        rows.append(row)
    summ = dict(length=n, mean=str(Fr(sum(c[-1] for _, c in cyc), n)),
                h9_r4_sat=sum(r['h9_r4'] == 'SAT' for r in rows))
    for r in r9:
        summ[f'h9_r{r}_unsat'] = sum(x[f'h9_r{r}'] == 'UNSAT' for x in rows)
    for r in radii10:
        summ[f'h10_r{r}_dead_pairs'] = sum(x[f'h10_r{r}_dead'] for x in rows)
    return summ, rows


def rigor(lams, maxit=3000):
    """BF from 0 at P/Q (best 233 split where lambda > 974/226, else best 234 split)."""
    S, O, K = build()
    out = []
    for lam in lams:
        b = best_pq233(lam)
        if b is None:
            P, Q, B = k7.best_pq(lam); target = 234
        else:
            P, Q, B, _ = b; target = 233
        L = 2 ** B - 1
        t = time.time()
        conv, pi, pred, it = K.bf(P, Q, 10 ** 9, maxit=maxit)
        rng = int(-pi.min())
        Bn = max(rng, 1).bit_length()
        rec = dict(lam=lam, P=P, Q=Q, target=target, B_allowed=B, converged=bool(conv), bf_rounds=int(it),
                   range=rng, range_units=round(rng / Q, 3), allowed_units=round(L / Q, 3),
                   bound_with_range=bound(P, Q, Bn) if conv else None, seconds=round(time.time() - t))
        print(json.dumps(rec), flush=True)
        out.append(rec)
        del pi, pred
    return out


def core_edges(K, edges):
    """Cyclic core of a list of (X index, flat count) edges: (kept list, U, V)."""
    U = np.array([K.XE[i][0] * NT + fl // 6 for i, fl in edges], np.int64)
    V = np.array([K.XE[i][1] * NT + fl % NT for i, fl in edges], np.int64)
    keep = np.ones(len(edges), bool)
    while len(edges):
        hin = set(V[keep].tolist()); hout = set(U[keep].tolist())
        k2 = keep & np.array([u in hin for u in U.tolist()]) & np.array([v in hout for v in V.tolist()])
        if k2.sum() == keep.sum():
            break
        keep = k2
    idx = np.flatnonzero(keep)
    return [edges[j] for j in idx], U[idx], V[idx]


def satcore(maxpairs=20000):
    """At the current minimum mean: the subgraph of tight edges whose H9 (radius 4) is SAT, its
    cyclic core, then (a) H9 at radius 5 on its edges, (b) H10 (radius 4) on its consecutive
    pairs; does a cycle survive each test?  (b) is the k8 automaton restricted to this core."""
    S, O, K = build()
    K._k6set = set()
    H = Howard(K); H.run(verbose=False)
    lam, cyc = H.min_cycle()
    Ti, Tf = H.tight(float(lam))
    sat, und = [], 0
    for i, fl in zip(Ti.tolist(), Tf.tolist()):
        st = O.status(k7.h9_key(K.X[i], digits(fl, 7)))
        if st == 'SAT':
            sat.append((i, fl))
        elif st is None:
            und += 1
    E, U, V = core_edges(K, sat)
    out = dict(lam=str(lam), tight0=len(Ti), tight0_sat=len(sat), tight0_undecided=und, sat_core_edges=len(E),
               sat_core_states=len(set(U.tolist()) | set(V.tolist())))
    print(json.dumps(out), flush=True)
    # (a) radius 5
    r5 = []
    for i, fl in E:
        st = O.get(k7.h9_key(K.X[i], digits(fl, 7)), radius=5, tlim=120.0)
        r5.append(st)
    O.flush()
    keep5 = [e for e, st in zip(E, r5) if st != 'UNSAT']
    E5, _, _ = core_edges(K, keep5)
    out.update(r5_unsat=sum(st == 'UNSAT' for st in r5), r5_sat=sum(st == 'SAT' for st in r5),
               r5_timeout=sum(st == 'TIMEOUT' for st in r5), r5_core_edges=len(E5))
    print(json.dumps(out), flush=True)
    # (b) H10 on consecutive pairs of core edges (line graph)
    byU = {}
    for j, u in enumerate(U.tolist()):
        byU.setdefault(u, []).append(j)
    pairs = [(a, b) for a in range(len(E)) for b in byU.get(int(V[a]), [])]
    out['pairs'] = len(pairs)
    alive, npair, dead = [], 0, 0
    for a, b in pairs[:maxpairs]:
        (i, fl), (i2, fl2) = E[a], E[b]
        opts = options10(K.X[i], digits(fl, 7), K.X[i2], digits(fl2, 7))
        sts = [O.get(k, tlim=120.0) for k in opts]
        ok = any(st != 'UNSAT' for st in sts)
        dead += not ok
        if ok:
            alive.append((a, b))
        npair += 1
        if npair % 200 == 0:
            O.flush(); print(f'  pairs {npair}/{len(pairs)}, dead {dead}', flush=True)
    O.flush()
    # cyclic core of the line graph
    A = set(alive)
    while True:
        hin = {b for a, b in A}; hout = {a for a, b in A}
        A2 = {(a, b) for a, b in A if a in hin and b in hout}
        if len(A2) == len(A):
            break
        A = A2
    out.update(pairs_tested=npair, pairs_dead=dead, h10_core_pairs=len(A), h10_complete=npair == len(pairs))
    print('SATCORE', json.dumps(out), flush=True)
    with open(os.path.join(D, 'satcore233.jsonl'), 'a') as f:
        f.write(json.dumps(out) + '\n')
    return out


def sizes():
    """k7 product statistics and the k8 sizes they imply (a k8 state = an allowed k7 transition)."""
    S, O, K = build()
    nX = K.nX
    ext10 = []
    for X in K.X:
        n = 0
        for d in range(min(max(X) + 2, 9)):
            if k7.GA.induced(tuple(X) + (d,)):
                n += 1
        ext10.append(n)
    live7 = int(K.alive.sum())
    ext9 = [0] * K.nE
    for i, (e, e2) in enumerate(K.XE):
        ext9[e] += 1
    eval7 = sum(int(K.alive[e].sum()) * ext9[e] * 6 for e in range(K.nE))
    allowed = []
    for i in range(nX):
        allowed.append(int(K.mask(i).sum()))
    live8 = sum(allowed)
    eval8 = sum(a * n * 6 for a, n in zip(allowed, ext10))
    out = dict(shapes8=K.nE, shapes9=nX, shapes10=sum(ext10), k7_full=K.nE * NT, k7_live=live7,
               k7_evaluations=eval7, k7_allowed_transitions=live8,
               k8_full=nX * N7, k8_live=live8, k8_full_transitions=sum(ext10) * 6 ** 8, k8_evaluations=eval8,
               k8_pot_rows=nX * 6, k8_pot_fields_per_row=6 ** 6)
    print(json.dumps(out), flush=True)
    json.dump(out, open(os.path.join(D, 'sizes233.json'), 'w'), indent=1)
    return out


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd')
    ap.add_argument('--hours', type=float, default=1.0)
    ap.add_argument('--maxtest', type=int, default=3000)
    ap.add_argument('--gen', default='h9')
    ap.add_argument('--tag', default='run')
    ap.add_argument('--delta', type=float, default=0.0)
    ap.add_argument('--R', type=float, default=0.0)
    ap.add_argument('--lams', nargs='+', type=float, default=[4.17])
    a = ap.parse_args()
    if a.cmd == 'mcm':
        S, O, K = build()
        K._k6set = set()
        H = Howard(K)
        H.run()
        lam, cyc = H.min_cycle()
        print('MCM', lam, float(lam), len(cyc), [c[-1] for _, c in cyc])
        print([(K.X[i], c) for i, c in cyc])
        I, Fl = H.tight(float(lam))
        print('tight core edges', len(I))
        for de, R in ((0.01, 0.5), (0.02, 1.0), (0.05, 2.0)):
            I, Fl = H.tight(float(lam), de, R)
            print('near-critical', de, R, len(I))
    elif a.cmd == 'satcore':
        satcore()
    elif a.cmd == 'sizes':
        sizes()
    elif a.cmd == 'loop':
        loop(a.hours, a.maxtest, a.gen, a.tag, a.delta, a.R)
    elif a.cmd == 'rigor':
        rigor(a.lams)
    elif a.cmd == 'ceiling':
        S, O0, keys6, newk = P4.pool()
        O = Oracle(S)
        recs = [json.loads(l) for l in open(ROUNDS)]
        cr = [r for r in recs if r.get('ceiling') and (a.tag == 'run' or r['tag'] == a.tag)][-1]
        summ, rows = ceiling_test(O, cr['cycle'])
        summ['tag'] = cr['tag']
        print('SUMMARY', json.dumps(summ), flush=True)
        with open(os.path.join(D, 'ceiling233.jsonl'), 'a') as f:
            f.write(json.dumps(dict(summary=summ, rows=rows), separators=(',', ':')) + '\n')


if __name__ == '__main__':
    main()
