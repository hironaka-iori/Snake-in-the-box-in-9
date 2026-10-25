"""Seven-centre (k = 7) direction automaton: the full product the Lean check enumerates.

State  (8-direction canonical shape C = d0..d7, lumped counts t = a2..a7)     132 x 6^6
Step   label d8 (canonical w.r.t. C, < 9) and new count s = a8; the 9-direction window
       X = C ++ [d8] (a 9-RGS, 505 induced ones) is tested by
         (k6)  windows of 3..7 directions ending at the new vertex, fully counted (2..6
               counts), both orientations -- the k6 table, unchanged;
         (F8)  the 8-direction window X[1:] with all 7 counts a2..a8, both orientations;
         (H9)  the 9-direction window X with counts a2..a8 and its first interior vertex
               (a1) uncounted.  Key form: reversed ("uncounted last"), so the key
               (canon(rev X), rev counts) is literally Refuted (winOf ds) (boundsOf syms)
               with 7 bounds for 8 centres (centresOf counts the first 7 only).
       and otherwise  P + pot(next) <= Q s + pot(cur).
Closed set: a state whose OWN k6 windows (3..7 directions ending at its last vertex, counts
       from t) are excluded never occurs in a snake (those are windows of the snake), so the
       check may skip it; the transitions in the product are those with a live source.  A
       state is live iff it is an allowed k6 transition (index e*6^6 + x, fp.Product layout),
       so the k7 product here = line graph of the allowed k6 transitions + F8/H9 cuts.
Bound (telescoping as total_bound6, one more step of memory):
       (P + 35 Q) m + 7 Q <= 9171 Q + 8 P + 2^B - 1.
"""
import sys, os, json, time, gzip
sys.dont_write_bytecode = True
for _v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_v] = '1'
import numpy as np
import importlib.util

HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
for p in ('23-k6-lean/full_product', '23-k6-lean/share_bonus', '10-window-aggregate/scripts',
          '11-local-ceiling/k6_loop', '23-k6-lean/scripts'):
    sys.path.insert(0, os.path.join(MS, p))
import fp as FP          # noqa: E402
import gen_lean_automaton6 as GA   # noqa: E402
import wincert as W      # noqa: E402
from refine import key as rkey, canon   # noqa: E402

SCR = os.environ.get('SCR', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/'
                     '9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/plan234')
NC, NT = 6 ** 5, 6 ** 6
N7 = 6 ** 7
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)
ORACLE = os.path.join(HERE, 'data', 'oracle_k7.jsonl.gz')


def rss_mb():
    for l in open('/proc/self/status'):
        if l.startswith('VmRSS'):
            return int(l.split()[1]) / 1024


def guard():
    """Pause while the machine is short of memory or disk (resource rules)."""
    while True:
        av = int(open('/proc/meminfo').read().split('MemAvailable:')[1].split()[0]) / 2 ** 20
        st = os.statvfs('/')
        free_mb = st.f_bavail * st.f_frsize / 2 ** 20
        if av >= 3 and free_mb >= 500:
            return
        print(f'guard: avail {av:.1f} GB, disk {free_mb:.0f} MB: pausing', flush=True)
        time.sleep(60)


def bound(P, Q, B):
    return (9171 * Q + 8 * P + 2 ** B - 1 - 7 * Q) // (P + 35 * Q)


def status():
    spec = importlib.util.spec_from_file_location(
        'refine_share_k6', os.path.join(MS, '23-k6-lean', 'share_bonus', 'refine_share.py'))
    RS = importlib.util.module_from_spec(spec); spec.loader.exec_module(RS)
    return RS.status()


def cidx(t):
    acc = 0
    for s in t:
        acc = acc * 6 + (s - 1)
    return acc


def digits(x, n):
    return tuple(x // 6 ** k % 6 + 1 for k in range(n - 1, -1, -1))


# ------------------------------------------------------------------ new keys
def h9_key(X, c):
    """Canonical H9 key of the step window X (9 dirs) with counts c = a2..a8."""
    return ('H', canon(tuple(reversed(X))), tuple(reversed(c)))


def f8_key(X, c):
    c8, al = rkey(tuple(X[1:]), tuple(LUMP[s] for s in c))
    return ('F', c8, tuple(GA.sym_of(a) for a in al))


def encoding(k):
    kind, ds, syms = k
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ 1 << d)
    al = [LUMP[s] for s in syms] + ([None] if kind == 'H' else [])
    return W.Encoding(vs, al, 4)


def decide(k):
    enc = encoding(k)
    t = time.time()
    st, _, cuts = W.decide(enc, certify=False)
    return st, time.time() - t


class Oracle:
    def __init__(self):
        self.st, self.sec = {}, {}
        if os.path.exists(ORACLE):
            for l in gzip.open(ORACLE, 'rt'):
                r = json.loads(l)
                k = (r['kind'], tuple(r['dirs']), tuple(r['syms']))
                self.st[k] = r['result']; self.sec[k] = r['seconds']
        self.buf = []

    def get(self, k):
        if k not in self.st:
            guard()
            st, sec = decide(k)
            self.st[k] = st; self.sec[k] = sec
            self.buf.append(dict(kind=k[0], dirs=list(k[1]), syms=list(k[2]), result=st,
                                 seconds=round(sec, 3)))
            if len(self.buf) >= 200:
                self.flush()
        return self.st[k]

    def flush(self):
        if self.buf:
            with gzip.open(ORACLE, 'at') as f:
                for r in self.buf:
                    f.write(json.dumps(r) + '\n')
            self.buf = []


# ------------------------------------------------------------------ product
class K7:
    def __init__(self, S=None, keys6=None):
        t0 = time.time()
        self.S = S if S is not None else status()
        self.Pr = Pr = FP.Product()
        self.keys6 = keys6 if keys6 is not None else self.S.unsat()
        for k in self.keys6:
            Pr.apply(k)
        self.alive = (Pr.CNT == 0)                       # (nE, NT): live k7 states
        self.nE = Pr.nE
        m8 = {x[3]: e for e, x in enumerate(Pr.ext)}
        self.X, self.XE = [], []
        for e, x in enumerate(Pr.ext):
            ds = x[3]
            for d in range(min(max(ds) + 2, 9)):
                X = ds + (d,)
                if GA.induced(X):
                    self.X.append(X); self.XE.append((e, m8[canon(X[1:])]))
        self.nX = len(self.X)
        self.xid = {X: i for i, X in enumerate(self.X)}
        # F8 lookup: canonical 8-window (either orientation) -> [(X index, orientation)]
        self.f8idx = {}
        for i, X in enumerate(self.X):
            w = X[1:]
            self.f8idx.setdefault(canon(w), []).append((i, 0))
            self.f8idx.setdefault(canon(tuple(reversed(w))), []).append((i, 1))
        self.newcnt = np.zeros((self.nX, N7), np.uint8)   # F8/H9 exclusion counts
        self.newkeys = set()
        print(f'k7: {self.nE} 8-shapes, {self.nX} 9-shapes, {int(self.alive.sum())} live states, '
              f'{len(self.keys6)} k6 keys, {time.time() - t0:.0f}s, rss {rss_mb():.0f} MB', flush=True)

    def hits_new(self, k):
        """(X index, 7-count tuple in step order) excluded by an F8/H9 key."""
        kind, ds, syms = k
        if kind == 'H':
            X = canon(tuple(reversed(ds)))
            i = self.xid.get(X)
            return [] if i is None else [(i, tuple(reversed(syms)))]
        out = []
        for i, o in self.f8idx.get(ds, ()):
            out.append((i, syms if o == 0 else tuple(reversed(syms))))
        return out

    def add_new(self, k):
        if k in self.newkeys:
            return
        self.newkeys.add(k)
        for i, c in self.hits_new(k):
            self.newcnt[i, cidx(c)] += 1

    def mask(self, i):
        e, e2 = self.XE[i]
        m = self.alive[e].reshape(6, NC, 1) & self.alive[e2].reshape(1, NC, 6)
        return m & (self.newcnt[i].reshape(6, NC, 6) == 0)

    def bf(self, P, Q, L, maxit=3000, extra=4, verbose=False):
        """Gauss-Seidel Bellman-Ford from 0 with weights Q s - P over all transitions with a
        live source.  Returns (converged, pi, pred, rounds); pred = X*6 + t0 (or -1)."""
        pi = np.zeros((self.nE, NT), np.int32)
        pred = np.full((self.nE, NT), -1, np.int32)
        w = (Q * np.arange(1, 7) - P).astype(np.int32)
        BIG = np.int32(2 ** 30)
        masks = [self.mask(i) for i in range(self.nX)]
        dirty = np.ones(self.nE, bool)
        first_bad = None
        for it in range(maxit):
            nd = np.zeros(self.nE, bool)
            for i in range(self.nX):
                e, e2 = self.XE[i]
                if not dirty[e]:
                    continue
                cand = np.where(masks[i], pi[e].reshape(6, NC, 1) + w, BIG)
                am = cand.argmin(0)
                mn = np.take_along_axis(cand, am[None], 0)[0]
                tgt = pi[e2].reshape(NC, 6)
                upd = mn < tgt
                if upd.any():
                    tgt[upd] = mn[upd]
                    pred[e2].reshape(NC, 6)[upd] = (i * 6 + am[upd]).astype(np.int32)
                    nd[e2] = True
            dirty = nd
            if verbose:
                print(f'  bf {it}: min {int(pi.min())}, dirty {int(nd.sum())}', flush=True)
            if not nd.any():
                return True, pi, pred, it
            if first_bad is None and pi.min() < -L:
                first_bad = it
            if first_bad is not None and it >= first_bad + extra:
                return False, pi, pred, it
        return False, pi, pred, maxit

    def chain(self, pi, pred, node, maxlen=400):
        """Predecessor walk ending at node: list of (X index, 7 counts a2..a8), oldest first."""
        out, seen = [], set()
        while len(out) < maxlen:
            p = int(pred.flat[node])
            if p < 0 or node in seen:
                break
            seen.add(node)
            i, t0 = divmod(p, 6)
            e, e2 = self.XE[i]
            x2 = node % NT                                 # a3..a8
            c = (t0 + 1,) + digits(x2, 6)
            out.append((i, c))
            node = e * NT + cidx(c[:6])
        return out[::-1]


def free_keys():
    """k6 keys with a certificate already (or being) replayed: the 236/237 sets and keys_235."""
    sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'full_product'))
    import prune as PR
    fr = PR.certified() | {PR.lumped_of(d, a) for d, a in
                           json.load(open(os.path.join(MS, '23-k6-lean', 'full_product', 'keys_235.json')))['keys']}
    return sorted(fr)


def best_pq(lam, qmax=2000):
    """P/Q <= lam (float) and bits B with 2^B <= 227 P - 939 Q maximising the slack
    (2^B - 1)/Q in count units (the bound is then 234)."""
    best = None
    for Q in range(1, qmax + 1):
        P = int(lam * Q)
        g = 227 * P - 939 * Q
        if g < 2:
            continue
        B = g.bit_length() - 1
        sl = (2 ** B - 1) / Q
        if best is None or sl > best[3] + 1e-12:
            best = (P, Q, B, sl)
    P, Q, B, sl = best
    assert bound(P, Q, B) == 234 and bound(P, Q, B + 1) <= 235
    return P, Q, B


def loop(K, O, P, Q, B, hours, log, maxchains=1000, maxtest=1500):
    L = 2 ** B - 1
    t0 = time.time()
    while True:
        conv, pi, pred, it = K.bf(P, Q, L)
        rec = dict(time=time.strftime('%H:%M:%S'), P=P, Q=Q, B=B, converged=bool(conv), bf_rounds=int(it),
                   pi_min=int(pi.min()), new_keys=len(K.newkeys), decided=len(O.st), rss=round(rss_mb()))
        if conv and pi.min() >= -L:
            rec['done'] = True
            print(json.dumps(rec), flush=True); log.append(rec)
            return True, pi
        flat = pi.ravel()
        bad = np.flatnonzero(flat < -L)
        if len(bad) < 1000:                    # cycle regime: also the deepest nodes above -L
            bad = np.flatnonzero(flat < -(L // 2))
        if len(bad) == 0:
            bad = np.flatnonzero(flat < 0)
        bad = bad[np.argsort(flat[bad], kind='stable')][:maxchains]
        chains = [K.chain(pi, pred, int(x)) for x in bad]
        freq = {}
        for ch in chains:
            for tr in set(ch):
                freq[tr] = freq.get(tr, 0) + 1
        broken = [False] * len(chains)
        exhaustive = len(chains) <= 1000        # few bad walks (cycle regime): test all their transitions
        where = {}
        for ci, ch in enumerate(chains):
            for tr in set(ch):
                where.setdefault(tr, []).append(ci)
        order = sorted(freq, key=lambda tr: (-freq[tr], tr))
        tested = unsat = 0
        for tr in order:
            if all(broken[ci] for ci in where[tr]) and not exhaustive:
                continue
            if tested >= maxtest:
                break
            i, c = tr
            k = h9_key(K.X[i], c)
            known = k in O.st
            st = O.get(k)
            tested += not known
            if st == 'UNSAT':
                K.add_new(k); unsat += 1
                for ci in where[tr]:
                    broken[ci] = True
        rec.update(chains=len(chains), mean_len=round(float(np.mean([len(c) for c in chains])), 1),
                   tested=tested, cut=unsat, unbroken=int(len(broken) - sum(broken)),
                   seconds=round(time.time() - t0))
        print(json.dumps(rec), flush=True); log.append(rec)
        O.flush()
        if unsat == 0:
            return False, pi
        if time.time() - t0 > hours * 3600:
            return None, pi


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('cmd')
    ap.add_argument('--lams', nargs='+', type=float, default=[4.15])
    ap.add_argument('--hours', type=float, default=1.0)
    ap.add_argument('--base', default='all', help="k6 keys: 'all' known, or 'free' (certified 236/237 + keys_235)")
    a = ap.parse_args()
    if a.cmd == 'loop':
        S = status()
        K = K7(S, free_keys() if a.base == 'free' else None); O = Oracle()
        for k, st in O.st.items():                      # every known UNSAT F8/H9 key
            if st == 'UNSAT':
                K.add_new(k)
        log = []
        t0 = time.time()
        for lam in a.lams:
            P, Q, B = best_pq(lam)
            print(f'== lambda {P}/{Q} = {P / Q:.5f}, {B} bits, slack {(2 ** B - 1) / Q:.3f}', flush=True)
            ok, pi = loop(K, O, P, Q, B, a.hours - (time.time() - t0) / 3600, log)
            res = dict(P=P, Q=Q, B=B, ok=ok, new_keys=len(K.newkeys), decided=len(O.st),
                       unsat_decided=sum(1 for v in O.st.values() if v == 'UNSAT'),
                       pi_range=int(-pi.min()))
            print('RESULT', json.dumps(res), flush=True)
            with open(os.path.join(HERE, 'data', 'loop_rounds.jsonl'), 'a') as f:
                f.write(json.dumps(dict(result=res, rounds=log)) + '\n')
            log = []
            if not ok:
                break
        O.flush()


if __name__ == '__main__':
    main()
