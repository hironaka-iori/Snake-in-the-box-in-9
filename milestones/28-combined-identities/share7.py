"""Context share thresholds (milestone 28, "Refinement toward 232").

The step weight 120 A + S5 needs, per transition, a lower bound on the M = 12 share sum of the
trailing 5 centres n+3..n+7.  Milestone 28 took it from the 6-direction 5-centre window alone.  The
same sum can be bounded inside a longer window of the same step, which carries more constraints:

  ctx 7: the 7 directions ds[1:8] (centres n+2..n+7, counts t0..t5 = the step's 6 counts),
         share summed over the last 5 centres only;
  ctx 8: the 8 directions ds[0:8] (centres n+1..n+7; the count at n+1 is free, 1..21),
         share summed over the last 5 centres only.

Every step of a snake has exactly one such window, so S5(e) = max(5-window lb, ctx lb) is still a
lower bound of the share sum of the trailing 5-window and the arithmetic (*) of comb.py is unchanged.
A record is oriented (no reversal: the share centres are the trailing ones); it applies to the
transitions whose ds[8-ctx:8] has the same canonical labelling and whose counts are t.

Records (data/ctxshare_r232.jsonl[.gz]): dirs (ctx directions, canonical labels), t (6 lumped
counts), ctx, T, result (UNSAT: trailing share >= T), witness5 (trailing share of a SAT model),
seconds, nv, ncl.  The SAT encoding is wincert_share.ShareEncoding with the share totalizer built
only over the trailing 5 centres (same clause kinds, so the Lean RefutedShare bridge needs only a
centre-range parameter).
"""
import os, sys, json, gzip, time, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
import wincert_share as ws
from wincert import window_from_dirs

FILE = os.path.join(HERE, 'data', 'ctxshare_r232.jsonl')   # not oracle_share*: other readers glob that prefix
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)
FREE = (1, 21)
INF = 10 ** 6


class SubShareEncoding(ws.ShareEncoding):
    """ShareEncoding whose share totalizer covers only the centre indices in `share_ci`."""
    def __init__(self, window, alpha, radius, M, cap, share_ci):
        self.share_ci = set(share_ci)
        super().__init__(window, alpha, radius, M, cap)

    def build_share(self):
        X, B, M, cap = self.var, self.B, self.M, self.cap
        w = self.window
        self.sq, self.tots, self.qs, self.ulits = {}, [], [], []
        for ci in range(1, len(w) - 1):
            if ci not in self.share_ci:
                continue
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ 1 << kk
                Es = []
                for a, b in itertools.combinations(range(9), 2):
                    if kk in (a, b):
                        continue
                    sq = [q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b]
                    assert all(v in B for v in sq), 'radius too small for the share'
                    e = self.fresh(); Es.append(e); self.sq[(q, a, b)] = e
                    self.add([X[v] for v in sq] + [e], 'emptyE')
                nb = [q ^ 1 << t for t in range(9)]
                eT = len(self.tots); ge_e = self.totalizer(Es, up=True)
                dT = len(self.tots); ge_d = self.totalizer([X[v] for v in nb], up=False, down=True)
                nE = len(Es)
                tmax = min(cap + 1, M * nE)
                us = []
                for t in range(1, tmax + 1):
                    u = self.fresh(); us.append(u)
                    for dd in range(1, 10):
                        cneed = ws.ceil_div(t * dd, M)
                        if cneed > nE:
                            continue
                        cl = [u]
                        if cneed >= 1:
                            cl.append(-ge_e[cneed])
                        if dd <= 8:
                            cl.append(ge_d[dd + 1])
                        self.add(cl, 'shareCl')
                self.ulits += us
                self.qs.append(dict(c=ci, kk=kk, q=q, eT=eT, dT=dT, tmax=tmax, u=us))
        self.capT = len(self.tots)
        o = self.totalizer(self.ulits, up=True, limit=cap + 1)
        if len(o) - 1 >= cap + 1:
            self.add([-o[cap + 1]], 'shareCap')
        self.nshare_vars = self.nv - self.nbase_vars


def trailing_share(window, sel, nshare=5, M=12):
    """Exact share of the last `nshare` centres of a window for a selection."""
    S = set(sel); tot = 0
    for ci in range(len(window) - 1 - nshare, len(window) - 1):
        c = window[ci]
        used = {(c ^ window[ci - 1]).bit_length() - 1, (c ^ window[ci + 1]).bit_length() - 1}
        for kk in range(9):
            if kk in used:
                continue
            q = c ^ 1 << kk
            if q in S:
                continue
            e0 = sum(1 for a, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            tot += (M * e0) // d
    return tot


def encode(dirs, t, T, ctx):
    """dirs: ctx directions; t: the 6 lumped counts of the last 6 centres."""
    w = window_from_dirs(list(dirs))
    al = [LUMP[s] for s in t]
    if ctx == 8:
        al = [FREE] + al
    al = ws.alpha_arg(al)
    k = len(w) - 2
    return SubShareEncoding(w, al, 4, 12, T - 1, range(k - 4, k + 1))


def thr(dirs, t, T, ctx, tl=60, path=None):
    t0 = time.time()
    enc = encode(dirs, t, T, ctx)
    build = time.time() - t0
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(dirs), t=list(t), ctx=ctx, T=T, kind='thr_ctx', result=st,
             witness5=trailing_share(enc.window, sel) if sel else None, cuts=cuts, seconds=round(sec, 1),
             build=round(build, 1), nv=enc.nv, ncl=len(enc.clauses))
    if path is not False:
        with open(path or FILE, 'a') as f:
            f.write(json.dumps(r) + '\n')
    return r


def records():
    out = []
    B = FILE.replace('_r232.', '_r232b.')            # second run (toward 231)
    F = FILE.replace('_r232.', '_r231.')             # farm toward 231 (farm231.py merge)
    for f in (FILE + '.gz', FILE, B + '.gz', B, F + '.gz'):
        if os.path.exists(f):
            for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
                out.append(json.loads(l))
    return out


class Ctx:
    """State per (ctx, canonical dirs, t): lb, ub (witness), fail (smallest timed-out T)."""
    def __init__(self):
        self.st = {}
        for r in records():
            self.apply(r)

    def get(self, k):
        return self.st.setdefault(k, dict(lb=0, ub=INF, fail=INF))

    def apply(self, r):
        s = self.get((r['ctx'], tuple(r['dirs']), tuple(r['t'])))
        if r['result'] == 'UNSAT':
            s['lb'] = max(s['lb'], r['T'])
        elif r['result'] == 'SAT':
            s['ub'] = min(s['ub'], r['witness5'])
        elif r['result'] == 'TIMEOUT':
            s['fail'] = min(s['fail'], r['T'])


def ctx_index(Pr, canon):
    """(ctx, canonical dirs) -> list of ext indices e whose last ctx directions have that form."""
    I = {}
    for e, (_, _, _, ds) in enumerate(Pr.ext):
        for ctx in (7, 8):
            I.setdefault((ctx, canon(tuple(ds[8 - ctx:]))), []).append(e)
    return I


def apply_all(G, Pr, canon, cnt_idx, NT, np):
    """Raise G['S5'] by every UNSAT context record."""
    I = ctx_index(Pr, canon)
    n = 0
    for (ctx, c, t), s in Ctx().st.items():
        if s['lb'] <= 0:
            continue
        p = positions(G, I, ctx, c, t, cnt_idx, NT, np)
        G['S5'][p] = np.maximum(G['S5'][p], s['lb']); n += len(p)
    return n


def positions(G, I, ctx, c, t, cnt_idx, NT, np):
    es = I.get((ctx, tuple(c)), [])
    if not es:
        return np.zeros(0, np.int64)
    g = np.array(es, np.int64) * NT + cnt_idx(tuple(t))
    p = np.searchsorted(G['G'], g)
    m = p < len(G['G'])
    p, g = p[m], g[m]
    return p[G['G'][p] == g]
