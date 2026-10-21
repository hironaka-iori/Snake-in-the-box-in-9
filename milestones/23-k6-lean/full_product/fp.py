"""Plain (radius-4, UNSAT-only) refinement of the k6 automaton on the FULL product.

The product is exactly the one the Lean k6 shard check enumerates
(../scripts/gen_lean_automaton6.py: `shapes7`, `transitions`): 34 canonical 7-direction
shapes x 6^5 lumped counts = 264,384 states; a step is one more direction d and count s,
allowed unless a window of 3..7 directions (2..6 counts) ending at the new vertex is an
exclusion key, in either orientation.  Labels d above max(shape)+1 give the same transition
as d = max(shape)+1, so only canonical labels are enumerated here (the generator itself is
run on the final set to confirm).

Target: lambda = 4 with a potential of range <= LIM (= 7, 3 bits), i.e. no walk of the full
product has weight sum(s - 4) < -LIM.  (With (num+35 den) m + 6 den <= 9171 den + 7 num +
2^bits - 1 this gives m <= 235.)  The integer Bellman-Ford potential started from 0 has the
least possible range, so the target holds iff Bellman-Ford converges with min >= -LIM.

Round: Bellman-Ford with predecessor edges; every node with pi < -LIM gives (by the usual
telescoping argument) a walk of weight < -LIM or a negative cycle along its predecessor
chain.  The edges of those walks are tested, most frequent first: the untested suffix
windows of the edge (2..6 counts, smallest first), stopping at the first UNSAT.  A walk
none of whose edges can be excluded (every 6-window SAT or timed out) is an obstruction.

Exclusions known before the run (all radius 4, plain, merged by k6loop.Plain plus the
k6_w3 and k6_w3_loop plain logs); UNSAT keys with non-lumped count ranges are expanded to
the lumped keys they contain (src 'derived': such a key still needs its own certificate).
New calls go to oracle_full.jsonl (k6loop record format); rounds to rounds.jsonl.

usage: nice -n 19 python fp.py loop HOURS [MAXTEST]   |   fp.py eval
"""
import sys, os, json, time, gzip, itertools
sys.dont_write_bytecode = True
for v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[v] = '1'
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 'k6_loop'))
sys.path.insert(0, os.path.join(MS, '23-k6-lean', 'scripts'))
import k6loop as K6
import gen_lean_automaton6 as GA
from refine import key as rkey, canon

SCR = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/k6full'
ORACLE = os.path.join(HERE, 'oracle_full.jsonl')
ROUNDS = os.path.join(HERE, 'rounds.jsonl')
NC, NT = GA.NC, GA.NT
LIM = int(os.environ.get('LIM', 7))
LUMP = {i: (i, i) for i in range(1, 6)}; LUMP[6] = (6, 21)


def rss_mb():
    for l in open('/proc/self/status'):
        if l.startswith('VmRSS'):
            return int(l.split()[1]) / 1024


def lkey(ds, syms):
    """Canonical lumped key (dirs, syms) of a window (k6loop/refine orientation rule)."""
    c, al = rkey(tuple(ds), tuple(LUMP[s] for s in syms))
    return c, tuple(GA.sym_of(a) for a in al)


def lumped_choices(a):
    lo, hi = a
    out = [s for s in range(1, 6) if lo <= s <= hi]
    if lo <= 6 and hi >= 21:
        out.append(6)
    return out


# ------------------------------------------------------------------ statuses
class Status:
    def __init__(self):
        P = K6.Plain()
        files = [os.path.join(MS, '22-global-arguments', 'k6_w3', 'data', 'plain_k6w3.jsonl'),
                 os.path.join(MS, '22-global-arguments', 'k6_w3_loop', 'data', 'plain_loop.jsonl.gz'),
                 ORACLE]
        for f in files:
            if not os.path.exists(f):
                continue
            for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
                r = json.loads(l)
                if r.get('kind') not in ('plain', 'plainrange'):
                    continue
                P.put(rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])), r['result'],
                      'here' if f == ORACLE else ('range' if r.get('src') == 'range' else 'k6w3'))
        K6.OPLAIN = ORACLE                       # new calls are logged here only
        self.P = P
        self.st = {}; self.src = {}
        for k, st in P.st.items():
            if not (2 <= len(k[1]) <= 6):
                continue
            ch = [lumped_choices(a) for a in k[1]]
            exact = all(len(c) == 1 and LUMP[c[0]] == a for c, a in zip(ch, k[1]))
            if exact:
                lk = lkey(k[0], tuple(c[0] for c in ch))
                self.st[lk] = st; self.src[lk] = P.src.get(k)
        for k, st in P.st.items():               # range UNSAT -> contained lumped keys
            if st != 'UNSAT' or not (2 <= len(k[1]) <= 6):
                continue
            ch = [lumped_choices(a) for a in k[1]]
            for t in itertools.product(*ch):
                lk = lkey(k[0], t)
                if self.st.get(lk) in (None, 'TIMEOUT'):
                    self.st[lk] = 'UNSAT'; self.src[lk] = 'derived'

    def unsat(self):
        return [k for k, s in self.st.items() if s == 'UNSAT']

    def test(self, k, tl):
        ds, syms = k
        r = self.P.test(rkey(ds, tuple(LUMP[s] for s in syms)), tl)
        self.st[k] = r['result']; self.src[k] = 'here'
        return r


# ------------------------------------------------------------------ product
class Product:
    def __init__(self):
        self.shp = GA.shapes7()
        s7 = {c: i for i, c in enumerate(self.shp)}
        self.ext = []                             # (i, d, j, ds)
        for i, c in enumerate(self.shp):
            for d in range(min(max(c) + 2, 9)):
                ds = c + (d,)
                if GA.induced(ds):
                    self.ext.append((i, d, s7[canon(ds[1:])], ds))
        self.nE = len(self.ext)
        self.n = len(self.shp) * NC
        self.idx = {}                             # (canon dirs, w) -> [(e, orient)]
        for e, (_, _, _, ds) in enumerate(self.ext):
            for w in range(2, 7):
                dd = ds[-(w + 1):]
                self.idx.setdefault((canon(dd), w), []).append((e, 0))
                self.idx.setdefault((canon(tuple(reversed(dd))), w), []).append((e, 1))
        self.Ei = np.array([x[0] for x in self.ext], np.int64)
        self.Ej = np.array([x[2] for x in self.ext], np.int64)
        self.CNT = np.zeros((self.nE, NT), np.uint16)

    def hits(self, k):
        """Distinct (e, pattern) a key excludes: transitions of ext e whose last w counts = pattern."""
        c, t = k; w = len(t); out = set()
        for e, o in self.idx.get((c, w), ()):
            out.add((e, t if o == 0 else tuple(reversed(t))))
        return out

    def apply(self, k, delta=1):
        w = len(k[1])
        for e, pat in self.hits(k):
            A = self.CNT[e].reshape((6,) * 6)
            A[(slice(None),) * (6 - w) + tuple(p - 1 for p in pat)] += delta

    def edges_of(self, k):
        """Global ids e*NT + x of the transitions a key excludes."""
        w = len(k[1]); out = []
        base = np.arange(6 ** (6 - w), dtype=np.int64) * 6 ** w
        for e, pat in self.hits(k):
            off = GA.cnt_idx(pat)
            out.append(e * NT + base + off)
        return np.concatenate(out) if out else np.zeros(0, np.int64)

    def uvw(self, g):
        e = g // NT; x = g % NT
        return self.Ei[e] * NC + x // 6, self.Ej[e] * NC + x % NC, (x % 6 + 1)

    def windows(self, g):
        """The suffix window keys (2..6 counts) of transition g, smallest first."""
        e = int(g // NT); x = int(g % NT)
        ds = self.ext[e][3]
        t = tuple(x // 6 ** k % 6 + 1 for k in range(5, -1, -1))
        return [lkey(ds[-(w + 1):], t[-w:]) for w in range(2, 7)]

    def bf(self, P=4, Q=1, lim=LIM, maxit=400, extra=6, allowed=None):
        """Bellman-Ford for weights Q s - P on the allowed transitions.  Returns
        (converged, pi, pred, iterations)."""
        if allowed is None:
            allowed = (self.CNT == 0).ravel()
        g = np.flatnonzero(allowed)
        u, v, s = self.uvw(g)
        w = (Q * s - P).astype(np.int32)
        o = np.argsort(v, kind='stable')
        g, u, v, w = g[o], u[o].astype(np.int32), v[o].astype(np.int32), w[o]
        del o
        uv, starts = np.unique(v, return_index=True)
        pi = np.zeros(self.n, np.int32); pred = np.full(self.n, -1, np.int64)
        first_bad = None
        for it in range(maxit):
            cand = pi[u] + w
            mins = np.minimum.reduceat(cand, starts)
            upd = mins < pi[uv]
            if not upd.any():
                return True, pi, pred, it
            um = np.zeros(self.n, bool); um[uv[upd]] = True
            pi[uv[upd]] = mins[upd]
            m = um[v] & (cand == pi[v])
            pred[v[m]] = g[m]
            if first_bad is None and pi.min() < -lim:
                first_bad = it
            if first_bad is not None and it >= first_bad + extra:
                break
        return False, pi, pred, it

    def chain(self, pi, pred, x, maxlen=600):
        """Predecessor chain into node x: (edges in walk order, is_cycle)."""
        seen = {}; seq = []
        while pred[x] >= 0 and x not in seen and len(seq) < maxlen:
            seen[x] = len(seq); g = int(pred[x]); seq.append(g)
            x = int(self.uvw(np.array([g]))[0][0])
        if x in seen:
            return list(reversed(seq[seen[x]:])), True
        return list(reversed(seq)), False


def load_all(S, Pr):
    for k in S.unsat():
        Pr.apply(k)


def walk_info(Pr, chain):
    g = np.array(chain, np.int64)
    u, v, s = Pr.uvw(g)
    return [int(a) for a in s]


def round_(S, Pr, maxtest, tl, log):
    t0 = time.time()
    conv, pi, pred, it = Pr.bf()
    rec = dict(time=time.strftime('%H:%M:%S'), converged=bool(conv), bf_it=int(it), pi_min=int(pi.min()),
               allowed=int((Pr.CNT == 0).sum()), keys=sum(1 for v in S.st.values() if v == 'UNSAT'))
    if conv and pi.min() >= -LIM:
        rec['done'] = True; rec['range'] = int(-pi.min())
        return rec
    bad = np.flatnonzero(pi < -LIM)
    if len(bad) == 0:                       # not converged yet min ok: negative cycle somewhere deep
        bad = np.flatnonzero(pred >= 0)
    bad = bad[np.argsort(pi[bad], kind='stable')][:3000]
    freq = {}; chains = []; ncyc = 0
    for x in bad:
        ch, cyc = Pr.chain(pi, pred, int(x))
        ncyc += cyc
        chains.append((ch, cyc))
        for g in ch:
            freq[g] = freq.get(g, 0) + 1
    rec.update(violators=int((pi < -LIM).sum()), chains=len(chains), cycles=int(ncyc), chain_edges=len(freq))
    tested = unsat = 0; hard = set(); removed = set()
    for g in sorted(freq, key=lambda g: -freq[g]):
        if tested >= maxtest:
            break
        ok = False
        for k in Pr.windows(g):
            st = S.st.get(k)
            if st == 'UNSAT':
                ok = True; break
            if st is None:
                r = S.test(k, tl if len(k[1]) == 6 else tl / 2); tested += 1
                if r['result'] == 'UNSAT':
                    Pr.apply(k); unsat += 1; ok = True; break
        if ok:
            removed.add(g)
        else:
            hard.add(g)
    # obstructions: chains all of whose edges are hard
    obs = [c for c in chains if all(g in hard for g in c[0])]
    rec.update(tested=tested, unsat=unsat, removed=len(removed), hard_edges=len(hard), obstructions=len(obs),
               test_s=round(time.time() - t0, 1), rss=round(rss_mb()))
    if obs:
        ch, cyc = min(obs, key=lambda c: (not c[1], len(c[0])))
        rec['obstruction'] = dict(cycle=cyc, len=len(ch), counts=walk_info(Pr, ch),
                                  weight=int(sum(s - 4 for s in walk_info(Pr, ch))),
                                  windows6=[[list(Pr.windows(g)[-1][0]), list(Pr.windows(g)[-1][1])] for g in ch])
    if tested == 0:
        rec['stuck'] = True
    return rec


def main():
    mode = sys.argv[1]
    S = Status(); Pr = Product()
    load_all(S, Pr)
    srcs = {}
    for k, v in S.st.items():
        if v == 'UNSAT':
            srcs[S.src[k]] = srcs.get(S.src[k], 0) + 1
    print(f'{Pr.nE} extensions, {Pr.n} states; {sum(1 for v in S.st.values() if v == "UNSAT")} lumped UNSAT keys '
          f'{srcs}; rss {rss_mb():.0f} MB', flush=True)
    if mode == 'export':
        ks = sorted(S.unsat(), key=lambda k: (len(k[0]), k))
        json.dump(dict(keys=[[list(d), [list(LUMP[x]) for x in t]] for d, t in ks]), open(sys.argv[2], 'w'))
        print('wrote', len(ks)); return
    if mode == 'eval':
        conv, pi, pred, it = Pr.bf(maxit=2000, extra=10 ** 6)
        print(dict(converged=conv, it=it, pi_min=int(pi.min())), flush=True)
        return
    hours = float(sys.argv[2]); maxtest = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 30
    t_end = time.time() + hours * 3600
    rnd = sum(1 for _ in open(ROUNDS)) if os.path.exists(ROUNDS) else 0
    while time.time() < t_end:
        while K6.mem_gb() < 3.0:
            print('low memory, pausing', flush=True); time.sleep(60)
        rec = round_(S, Pr, maxtest, tl, None); rec['round'] = rnd; rnd += 1
        print(json.dumps({k: v for k, v in rec.items() if k != 'obstruction'}), flush=True)
        if 'obstruction' in rec:
            print('OBSTRUCTION', json.dumps(rec['obstruction']), flush=True)
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if rec.get('done') or rec.get('stuck'):
            break


if __name__ == '__main__':
    main()
