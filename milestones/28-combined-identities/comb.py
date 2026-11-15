"""Combined global identities on the k6 full product (milestone 28, solver/Python side only).

The automaton is exactly the one the Lean k6 check enumerates (../23-k6-lean/scripts/
gen_lean_automaton6.py, through ../23-k6-lean/full_product/fp.py): 34 canonical 7-direction shapes
x 6^5 lumped counts = 264,384 states; a step is a direction d and a new count s; a step is allowed
unless a window of 3..7 directions (2..6 counts) ending at the new vertex is an exclusion key.

Step n (n = 0 .. m-8) has the 8 directions ds = (state shape) ++ [d] and the 6 counts
t = (t0..t4, s) of the internal vertices n+2 .. n+7 (s = alpha at n+7).  Per step we keep three
integer weights, each a lower bound on a local quantity of the snake window:

  A(e)  = s                                       (sym alpha of the new vertex, exact)
  S5(e) = lb of the 5-centre M12 share sum of the trailing 5-window ds[2:8] / t[1:6]
          (share oracles of milestone 11; 0 where unknown)
  W6(e) = lb of the 6-centre w_3 charge sum (c(x) = sum_Q floor(12/|Q cap S|)) of the 6-window
          ds[1:8] / t, as ../22-global-arguments/k6_w3_loop/fullprod.py:
          max(lb6, lb5(left) + single(t5), single(t0) + lb5(right)), lb5 incl. the DP floor.

Identities (v = m + 1 vertices):
  [I_s]  sum_x (24 alpha + share12) + 840 (m+1) <= 221136      (ShareBridge.core_charge_sum_le, M=12;
         share >= 0 makes this imply the alpha identity sum alpha + 35 v <= 9214)
  [I_w]  sum_x c(x) <= 64512                                     (3-cube census, not in Lean)

Combined step weight for integers a, b >= 0:   w(e) = a (120 A + S5) + b W6.
Each 5-window [r, r+4], 3 <= r <= m-5, is the trailing window of exactly one step, each 6-window
[r, r+5], 2 <= r <= m-6, is the window of exactly one step, so (shares, c >= 0; alpha >= 1 at 1..6,
alpha >= 4 at the endpoints; c >= c1 = min single-centre floor at the 36 multiplicity deficits of
internal vertices 1..6 and m-5..m-1):
  sum_n w(n) <= 5 a (219960 - 840 m) + b (387072 - 36 c1).
With lambda = P/Q the minimum cycle mean of w and a potential of range R on the full product,
  Q sum_n w(n) >= P (m - 7) - R, hence
  (P + 4200 a Q) m <= Q (1099800 a + b (387072 - 36 c1)) + 7 P + R.               (*)
a = 1, b = 0, S5 = 0 is the k6 alpha chain times 120 (milestone 23: (P+35Q)m + 6Q <= 9171Q + 7P + R).
"""
import sys, os, json, time, gzip, itertools, math
sys.dont_write_bytecode = True
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
SCR = os.environ.get('LPSCR', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/lp')
for p in ('23-k6-lean/full_product', '23-k6-lean/scripts', '11-local-ceiling/k6_loop',
          '11-local-ceiling/s0_share_loop', '22-global-arguments/w3_survey', '22-global-arguments/k6_w3'):
    sys.path.insert(0, os.path.join(MS, p))
import fp                                     # Status, Product, lkey, LUMP
import gen_lean_automaton6 as GA
from refine import prune, canon
NC, NT = GA.NC, GA.NT
LUMP = fp.LUMP


def rss_mb():
    for l in open('/proc/self/status'):
        if l.startswith('VmRSS'):
            return int(l.split()[1]) / 1024


def disk_mb():
    s = os.statvfs('/'); return s.f_bavail * s.f_frsize / 2 ** 20


def log(*a):
    print(time.strftime('%H:%M:%S'), *a, flush=True)


def lumped_choices(a):
    return fp.lumped_choices(tuple(a))


# ------------------------------------------------------------------ share oracle (5-windows, M = 12)
def share_records():
    """Every 5-window share record of milestone 11 (refine_share semantics)."""
    import importlib.util
    spec = importlib.util.spec_from_file_location(
        'refine_share_m11', os.path.join(MS, '11-local-ceiling', 's0_share_loop', 'refine_share.py'))
    RS = importlib.util.module_from_spec(spec); spec.loader.exec_module(RS)
    O = RS.ShareOracle()                      # s0_radius4 E1 seeds + share_oracle.jsonl
    for f in (os.path.join(MS, '11-local-ceiling', 'k6_loop', 'oracle_share.jsonl'),
              os.path.join(MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle5_extra.jsonl'),
              os.path.join(HERE, 'data', 'oracle_share.jsonl'),
              os.path.join(HERE, 'data', 'oracle_share_bulk.jsonl'),
              os.path.join(HERE, 'data', 'oracle_share_r232.jsonl.gz'),
              os.path.join(HERE, 'data', 'oracle_share_r232.jsonl'),
              os.path.join(HERE, 'data', 'oracle_share_r232b.jsonl.gz'),
              os.path.join(HERE, 'data', 'oracle_share_r232b.jsonl'),
              os.path.join(HERE, 'data', 'oracle_share_r231.jsonl.gz')):     # farm231.py merge
        if not os.path.exists(f):
            continue
        for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
            r = json.loads(l)
            if len(r['alpha']) == 5:
                O.apply(r)
    return O


def dense_insert(D, c, t, v, n):
    """D[canon dirs][cnt_idx(t)] = max(., v), both orientations; t a tuple of lumped syms."""
    for cc, tt in ((canon(tuple(c)), tuple(t)), (canon(tuple(reversed(c))), tuple(reversed(t)))):
        arr = D.get(cc)
        if arr is None:
            arr = D[cc] = np.zeros(6 ** n, np.int64)
        x = GA.cnt_idx(tt)
        if v > arr[x]:
            arr[x] = v


def share_dense(certified_only=False):
    """Dense lb tables of the 5-centre M12 share, keyed by canonical 6-direction shape.
    certified_only: only the Lean-checked floors of origin/main (milestones 73, 152, 155)."""
    D = {}
    if not certified_only:
        O = share_records()
        for (ds, al), s in O.st.items():
            if s['lb'] <= 0 or len(al) != 5:
                continue
            for t in itertools.product(*[lumped_choices(a) for a in al]):
                dense_insert(D, ds, t, s['lb'], 5)
    for c, al, v in CERT_SHARE:
        for t in itertools.product(*[lumped_choices(a) for a in al]):
            dense_insert(D, c, t, v, 5)
    return D


FREE = (1, 21)
CERT_SHARE = [
    # universal 5-centre share floors proved in Lean on origin/main (either orientation)
    ((0, 1, 2, 0, 3, 2), [FREE] * 5, 16),       # milestone 152 (012032)
    ((0, 1, 2, 0, 3, 1), [FREE] * 5, 16),       # milestone 73 (012031)
    ((0, 1, 2, 3, 0, 4), [FREE] * 5, 16),       # milestone 73 (012304)
    ((0, 1, 2, 3, 1, 4), [FREE] * 5, 16),       # milestone 73 (012314)
    # milestone 155: 012032 with counts (4, <=4, 4, <=5, 3): share >= 17
    ((0, 1, 2, 0, 3, 2), [(4, 4), (1, 4), (4, 4), (1, 5), (3, 3)], 17),
]


# ------------------------------------------------------------------ w_3 oracle (fullprod.py logic)
def w3_setup():
    import w3survey as survey
    import refine_w3 as R
    K6W3 = os.path.join(MS, '22-global-arguments', 'k6_w3', 'data')
    K6W3L = os.path.join(MS, '22-global-arguments', 'k6_w3_loop', 'data')
    W3S = os.path.join(MS, '22-global-arguments', 'w3_survey', 'data')
    O = survey.Oracle(os.path.join(K6W3L, 'w3_loop_oracle.jsonl'))
    for f in (os.path.join(K6W3, 'w3_k6_oracle.jsonl'), os.path.join(W3S, 'w3_alpha_oracle.jsonl'),
              os.path.join(HERE, 'data', 'oracle_w3.jsonl')):
        if not os.path.exists(f):
            continue
        for l in open(f):
            O.apply(json.loads(l))
    sub = R.Sub()
    return survey, O, sub


def symt(a):
    a = tuple(a)
    if a[0] == a[1] and 1 <= a[0] <= 5:
        return a[0]
    if a == (6, 21):
        return 6
    return None


class W3Tables:
    def __init__(self):
        self.survey, self.O, self.sub = w3_setup()
        self.single = {s: self.sub.single_lb(LUMP[s]) for s in range(1, 7)}
        self.g5 = list(itertools.product(range(1, 7), repeat=5))
        g6 = np.array(list(itertools.product(range(1, 7), repeat=6)))
        self.B = {}
        self.lb6 = {}
        for k, st in self.O.st.items():
            if len(k[1]) != 6 or not st['lb']:
                continue
            s = tuple(symt(a) for a in k[1])
            if None in s:
                continue
            for c, t in ((k[0], s), (canon(tuple(reversed(k[0]))), tuple(reversed(s)))):
                x = GA.cnt_idx(t)
                d = self.lb6.setdefault(c, {})
                d[x] = max(d.get(x, 0), st['lb'])
        self.sF = np.array([self.single[s] for s in g6[:, 0]]); self.sL = np.array([self.single[s] for s in g6[:, 5]])
        self.iL = np.array([GA.cnt_idx(t) for t in g6[:, :5]]); self.iR = np.array([GA.cnt_idx(t) for t in g6[:, 1:]])
        self.A = {}

    def excl_keys(self):
        """w_3 solver calls that found the plain window infeasible (plain UNSAT, lumped)."""
        out = []
        for k, st in self.O.st.items():
            if st['excl']:
                s = tuple(symt(a) for a in k[1])
                if None not in s and 2 <= len(s) <= 6:
                    out.append(fp.lkey(k[0], s))
        return out

    def lb5_dense(self, c6):
        if c6 not in self.B:
            arr = np.empty(len(self.g5), np.int64)
            for x, t in enumerate(self.g5):
                k = self.survey.key(c6, [LUMP[s] for s in t])
                st = self.O.st.get(k)
                arr[x] = max(self.sub.floor5(k), st['lb'] if st else 0)
            self.B[c6] = arr
        return self.B[c6]

    def dense(self, c):
        if c not in self.A:
            w = np.maximum(self.lb5_dense(canon(c[0:6]))[self.iL] + self.sL,
                           self.sF + self.lb5_dense(canon(c[1:7]))[self.iR])
            for x, v in self.lb6.get(c, {}).items():
                w[x] = max(w[x], v)
            self.A[c] = w
        return self.A[c]


# ------------------------------------------------------------------ graph
def load_keyfile(path):
    if path == 'cert':
        return CERT_KEYS()
    d = json.load(gzip.open(path, 'rt') if path.endswith('.gz') else open(path))
    if 'cases' in d:
        ks = [(c['dirs'], c['alpha']) for c in d['cases'] if c.get('drat_trim_verified')]
    else:
        ks = d['keys'] if 'keys' in d else d
    out = []
    for e in ks:
        ds, al = e[0], e[1]
        ch = [lumped_choices(a) for a in al]
        for t in itertools.product(*ch):       # a range key excludes every lumped key it contains
            out.append(fp.lkey(tuple(ds), t))
    return out


def own_plain_unsat():
    """Plain UNSAT keys found by this milestone (data/oracle_plain.jsonl), lumped."""
    import glob
    out = []
    for f in sorted(glob.glob(os.path.join(HERE, 'data', 'oracle_plain*.jsonl'))
                    + glob.glob(os.path.join(HERE, 'data', 'oracle_plain*.jsonl.gz'))):
        for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
            r = json.loads(l)
            if r['result'] == 'UNSAT':
                for t in itertools.product(*[lumped_choices(a) for a in r['alpha']]):
                    out.append(fp.lkey(tuple(r['dirs']), t))
    return out


def CERT_KEYS():
    """Plain keys whose certificates are Lean-replayed today (the 237/236/235 chains)."""
    out = []
    for f in (os.path.join(MS, '10-window-aggregate', 'data', 'direction_certificates_r4b.json'),
              os.path.join(MS, '10-window-aggregate', 'data', 'direction_certificates_r4c.json'),
              os.path.join(MS, '23-k6-lean', 'full_product', 'keys_235.json')):
        out += load_keyfile(f)
    return sorted(set(out))


def build(keys='all', with_share=True, with_w3=True, certified_share=False, cache=False):
    """Arrays over the allowed transitions of the full product:
    U, V (int32 states), A (int8), S5 (int32), W6 (int32), G (int64 global ids e*NT + x)."""
    tag = f"{os.path.basename(keys)}_{int(with_share)}{int(with_w3)}{int(certified_share)}"
    npz = os.path.join(SCR, f'graph_{tag}.npz')
    if cache and os.path.exists(npz):
        z = np.load(npz)
        return {k: z[k] for k in z.files}
    t0 = time.time()
    Pr = fp.Product()
    if keys == 'all':
        S = fp.Status()
        ks = S.unsat() + own_plain_unsat()
        if with_w3:
            W3 = W3Tables()
            ks = list(set(ks) | set(W3.excl_keys()))
    else:
        ks = load_keyfile(keys)
    for k in set(ks):
        Pr.apply(k)
    log(f'{len(set(ks))} exclusion keys applied, {Pr.nE} extensions, {time.time()-t0:.0f}s rss {rss_mb():.0f}')
    if with_w3 and keys != 'all':
        W3 = W3Tables()
    SD = share_dense(certified_share) if with_share else {}
    log(f'share tables {len(SD)} shapes')
    x = np.arange(NT)
    Us, Vs, As, Ss, Ws, Gs = [], [], [], [], [], []
    zero5 = np.zeros(6 ** 5, np.int64)
    for e, (i, d, j, ds) in enumerate(Pr.ext):
        ok = Pr.CNT[e] == 0
        xs = x[ok]
        Us.append((i * NC + xs // 6).astype(np.int32)); Vs.append((j * NC + xs % NC).astype(np.int32))
        As.append((xs % 6 + 1).astype(np.int8)); Gs.append(e * NT + xs)
        Ss.append(SD.get(canon(ds[2:8]), zero5)[xs % (6 ** 5)].astype(np.int32))
        if with_w3:
            Ws.append(W3.dense(canon(ds[1:8]))[xs].astype(np.int32))
        else:
            Ws.append(np.zeros(len(xs), np.int32))
    G = dict(U=np.concatenate(Us), V=np.concatenate(Vs), A=np.concatenate(As), S5=np.concatenate(Ss),
             W6=np.concatenate(Ws), G=np.concatenate(Gs))
    G['n'] = np.array(len(Pr.shp) * NC)
    if with_share and not certified_share and os.environ.get('NOCTX') != '1':
        import share7                         # context share thresholds (Refinement toward 232)
        nctx = share7.apply_all(G, Pr, canon, GA.cnt_idx, NT, np)
        log(f'context share records applied to {nctx} transitions')
    if with_w3:
        G['c1'] = np.array(min(W3.single.values()))
    else:
        G['c1'] = np.array(0)
    log(f"{len(G['U'])} allowed transitions; {time.time()-t0:.0f}s rss {rss_mb():.0f}")
    if cache and disk_mb() > 400:
        os.makedirs(SCR, exist_ok=True)
        np.savez(npz, **G)
    return G


def live(G):
    """Indices of transitions on the live core (both endpoints have in- and out-edges)."""
    return np.nonzero(prune(int(G['n']), G['U'].astype(np.int64), G['V'].astype(np.int64)))[0]


# ------------------------------------------------------------------ minimum cycle mean
def _evaluate(nxt, cost):
    n = len(nxt)
    K = max(1, int(n).bit_length() + 1)
    J = nxt.copy()
    for _ in range(K):
        J = J[J]
    roots = np.unique(J)                       # nodes on policy cycles (all of them)
    eta = np.empty(n); val = np.zeros(n)
    oncyc = np.zeros(n, bool); oncyc[roots] = True
    done = np.zeros(n, bool)
    for r in roots:
        if done[r]:
            continue
        cyc = [int(r)]; y = int(nxt[r])
        while y != r:
            cyc.append(y); y = int(nxt[y])
        c = np.array(cyc)
        mu = cost[c].sum() / len(c)
        eta[c] = mu; done[c] = True
        # val[r] = 0, val[y] = cost[y] - mu + val[nxt y] backwards along the cycle
        acc = 0.0
        vv = np.empty(len(c))
        for t in range(len(c) - 1, 0, -1):
            acc = cost[c[t]] - mu + acc
            vv[t] = acc
        vv[0] = 0.0
        val[c] = vv
    eta_all = eta[J]
    # tree values by doubling: val(x) = sum_{i < 2^K} (cost(x_i) - eta) + val(x_{2^K})
    Jk = nxt.copy(); Sk = cost - eta_all
    for _ in range(K):
        Sk = Sk + Sk[Jk]
        Jk = Jk[Jk]
    vfin = np.where(oncyc, val, Sk + val[Jk])
    return eta_all, vfin


def howard(n, U, V, W, maxit=1000, verbose=False):
    """Minimum cycle mean by policy iteration (vectorised).  Every node must have an out-edge.
    Returns (mean float, list of edge indices (into the given arrays) of a minimum cycle)."""
    nodes, Uc = np.unique(U, return_inverse=True)
    Vc = np.searchsorted(nodes, V)
    assert (nodes[Vc] == V).all(), 'edge into a node without out-edges (prune first)'
    n = len(nodes)
    order = np.argsort(Uc, kind='stable')
    Us, Vs, Ws = Uc[order].astype(np.int64), Vc[order].astype(np.int64), W[order].astype(np.float64)
    starts = np.searchsorted(Us, np.arange(n))
    E = len(Us); ar = np.arange(E)
    pol = starts.copy()
    scale = max(1.0, float(np.abs(Ws).max()))
    eps = 1e-9 * scale
    for it in range(maxit):
        eta, val = _evaluate(Vs[pol], Ws[pol])
        e_eta = eta[Vs]
        m_eta = np.minimum.reduceat(e_eta, starts)
        b1 = m_eta < eta - eps
        e_val = Ws - e_eta + val[Vs]
        ok2 = e_eta <= m_eta[Us] + eps
        m_val = np.minimum.reduceat(np.where(ok2, e_val, np.inf), starts)
        b2 = (~b1) & (m_val < val - eps * 10)
        if not (b1.any() or b2.any()):
            break
        first1 = np.minimum.reduceat(np.where(e_eta <= m_eta[Us] + eps * 0.5, ar, E), starts)
        first2 = np.minimum.reduceat(np.where(ok2 & (e_val <= m_val[Us] + eps), ar, E), starts)
        pol = np.where(b1, first1, np.where(b2, first2, pol))
        if verbose:
            log(f'  howard it {it}: min eta {eta.min():.6f}, switches {int(b1.sum())}+{int(b2.sum())}')
    u0 = int(np.argmin(eta))
    seen = {}; x = u0; seq = []
    nxt = Vs[pol]
    while x not in seen:
        seen[x] = len(seq); seq.append(x); x = int(nxt[x])
    cyc = seq[seen[x]:]
    return float(eta.min()), [int(order[pol[y]]) for y in cyc]


def bellman_ford(n, U, V, Wt, max_iter=20000):
    """Integer BF from 0 (all nodes sources).  Returns (pi or None, rounds)."""
    order = np.argsort(V, kind='stable')
    Us, Vs, Ws = U[order].astype(np.int64), V[order].astype(np.int64), Wt[order].astype(np.int64)
    uv, starts = np.unique(Vs, return_index=True)
    pi = np.zeros(n, np.int64)
    for it in range(max_iter):
        cand = pi[Us] + Ws
        mins = np.minimum.reduceat(cand, starts)
        upd = mins < pi[uv]
        if not upd.any():
            return pi, it
        pi[uv[upd]] = mins[upd]
    return None, max_iter


# ------------------------------------------------------------------ arithmetic
def bound_m(P, Q, R, a, b, c1):
    """Largest m allowed by (*): (P + 4200 a Q) m <= Q (1099800 a + b (387072 - 36 c1)) + 7P + R."""
    num = Q * (1099800 * a + b * (387072 - 36 * c1)) + 7 * P + R
    return num // (P + 4200 * a * Q)


def bound_real(lam, a, b, c1, R_over_Q=0.0):
    """Real-valued m from (*) with lambda = lam (R/Q in weight units)."""
    return (1099800 * a + b * (387072 - 36 * c1) + 7 * lam + R_over_Q) / (lam + 4200 * a)


def weights(G, a, b, idx=None):
    A, S5, W6 = (G['A'], G['S5'], G['W6']) if idx is None else (G['A'][idx], G['S5'][idx], G['W6'][idx])
    return a * (120 * A.astype(np.int64) + S5) + b * W6.astype(np.int64)


def cycle_info(G, idx, cyc):
    """Readable description of a cycle (edge indices into the global arrays)."""
    shp = GA.shapes7()
    out = []
    for e in cyc:
        g = int(G['G'][e]); ext = g // NT; x = g % NT
        u = int(G['U'][e])
        t = [x // 6 ** k % 6 + 1 for k in range(5, -1, -1)]
        out.append(dict(shape=''.join(map(str, shp[u // NC])), counts=t, A=int(G['A'][e]),
                        S5=int(G['S5'][e]), W6=int(G['W6'][e]), g=g))
    return out


def step_windows(g, Pr=None):
    """(ext dirs ds, counts t, 5-window lumped key, 6-window lumped key) of global transition id g."""
    if Pr is None:
        Pr = _PR[0] if _PR else _PR.append(fp.Product()) or _PR[0]
    e = int(g) // NT; x = int(g) % NT
    ds = Pr.ext[e][3]
    t = tuple(x // 6 ** k % 6 + 1 for k in range(5, -1, -1))
    return ds, t, fp.lkey(ds[2:8], t[1:]), fp.lkey(ds[1:8], t)


_PR = []


def rkey_of(lk):
    """refine.key form (dirs, alpha ranges) of a lumped key."""
    from refine import key as rkey
    return rkey(tuple(lk[0]), tuple(LUMP[s] for s in lk[1]))
