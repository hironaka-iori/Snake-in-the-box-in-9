"""Memory-lean minimize_fast.py: the same window choice on LeanAutomaton's CSR arrays.

Same CLI semantics and output JSON as minimize_fast.py (--L --k --K --radius --escalate --avoid --lam
--start --prefer --tag), plus --out (output path) and --vb-max-edges (skip the exact walk bound, report
null, when the final graph has more edges).  Differences in the implementation only:

* graph: LeanAutomaton.edges (int32 V, uint8 W, int64 CSR starts; U and EXT are dropped at once), rebuilt
  from the kept set when needed (start, each pass without --start, end); freed during the greedy loop;
* min_start_potential / bellman_ford: the same Jacobi Bellman-Ford and binary search (leanmin_c.c,
  int32 potentials, only states changed in the last iteration are relaxed), same final checks
  (every edge has non-negative reduced cost, 0 <= pi <= D + Q*init);
* Blockers: the blocker count of (extension e, code) is the sum over window lengths c of
  T[(window shape, c)][low c digits] (plus T[(reversed shape, c)][reversed digits]), where T counts the
  kept windows of that shape covering each symbol tuple (palindromic shapes: covering it in either
  orientation, i.e. the union minimize_fast uses).  This is exactly minimize_fast's cnt, without any
  array over (extension, code); removable() runs in C over the codes the window blocks;
* minimum mean: prune_masked + LeanHowardGraph; walk bound: the same dynamic programme in C.

  python lean_minimize.py --L 8 --k 7 --K 7 --radius 3 --escalate 4 --start --lam 9/2 --prefer IDX
"""
import argparse, ctypes, json, os, resource, subprocess, sys, time
from collections import Counter
from fractions import Fraction as Fr
import numpy as np

SCRIPTS = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts'
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)
import refine                                                    # noqa: E402  (oracles looked up at call time)
from refine import DATA                                          # noqa: E402
from minimize_fast import sym_codes                              # noqa: E402
from lean_automaton import LeanAutomaton, LeanHowardGraph        # noqa: E402
from fastround import BlockMap, prune_masked                     # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
_lib = None


def _load():
    global _lib
    if _lib is None:
        src = os.path.join(HERE, 'leanmin_c.c'); so = os.path.join(HERE, 'leanmin_c.so')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.check_call(['cc', '-O2', '-shared', '-fPIC', '-o', so, src])
        lib = ctypes.CDLL(so)
        P = np.ctypeslib.ndpointer
        i64, i32 = ctypes.c_int64, ctypes.c_int
        I64, I32, U8, I16 = (P(np.int64, flags='C'), P(np.int32, flags='C'), P(np.uint8, flags='C'),
                             P(np.int16, flags='C'))
        lib.bf_jacobi.argtypes = [i64, I64, I32, U8, i64, i64, I32, I32, U8, i64, i32, I64]
        lib.bf_jacobi.restype = i64
        lib.check_pot.argtypes = [i64, I64, I32, U8, i64, i64, I32, i32, i64, I32, i64]
        lib.check_pot.restype = i64
        lib.removable.argtypes = [i64, I32, U8, i64, I64, i32, i32, i64, i64, I32, I32, I16, I64, I64,
                                  I32, I64, I32, i64, i64, I64]
        lib.removable.restype = i32
        lib.dp_step.argtypes = [i64, I64, I32, U8, I32, I32]
        lib.dp_step.restype = ctypes.c_int32
        _lib = lib
    return _lib


def rss_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss >> 10


# ---- graph -------------------------------------------------------------------------------------
class _Keys:
    """Oracle stand-in: exactly the given windows are exclusions."""
    def __init__(self, keys):
        self.known = {x: 'UNSAT' for x in keys}


def edges_vw(A, oracle, block_cells=1 << 21):
    """LeanAutomaton.edges without U and EXT: (starts int64[n+1], V int32, W uint8), the same edges in the
    same (source, extension, symbol) order.  5 B per edge plus the packed masks (1/8 B per candidate)."""
    T = A.forb_tables(oracle)
    ns, k, m1 = A.ns, A.k, A.m1
    nc = ns ** k
    by_shape = {}
    for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
        by_shape.setdefault(i, []).append(e)
    packed = {}
    deg = np.zeros(A.n, np.int64)
    for i, es in by_shape.items():
        M = np.empty((len(es), nc), bool)
        for j, e in enumerate(es):
            A._mask(A.ext[e][4], T, M[j])
        deg[i * m1:(i + 1) * m1] = M.reshape(len(es), m1, ns).sum(axis=(0, 2))
        packed[i] = np.packbits(M)
        del M
    starts = np.zeros(A.n + 1, np.int64)
    np.cumsum(deg, out=starts[1:])
    del deg
    E = int(starts[-1])
    V = np.empty(E, np.int32); W = np.empty(E, np.uint8)
    for i, es in by_shape.items():
        assert es == list(range(es[0], es[0] + len(es)))
        nE = len(es)
        M = np.unpackbits(packed.pop(i), count=nE * nc).view(bool).reshape(nE, m1, ns)
        nxt = np.array([A.ext[e][2] for e in es], np.int64)
        rows = max(1, block_cells // (nE * ns))
        for t0_ in range(0, m1, rows):
            t1_ = min(m1, t0_ + rows)
            f = np.flatnonzero(np.ascontiguousarray(M[:, t0_:t1_, :].transpose(1, 0, 2)))
            a = int(starts[i * m1 + t0_]); b = a + len(f)
            assert b == starts[i * m1 + t1_]
            t, r = np.divmod(f, nE * ns)
            j, w = np.divmod(r, ns)
            t += t0_
            V[a:b] = nxt[j] * m1 + (t * ns + w) % m1
            W[a:b] = w + 1
        del M
    return starts, V, W


class Graph:
    """Allowed edges of the kept set in CSR form (starts, V int32, W uint8)."""
    def __init__(self, A, keys):
        self.n = A.n
        self.starts, self.V, self.W = edges_vw(A, _Keys(keys))
        self.E = len(self.V)

    def min_mean(self):
        """minimize_fast: prune, Howard (cold) on the surviving edges, exact mean of the cycle found."""
        m = np.ones(self.E, np.uint8)
        prune_masked(self.n, self.starts, self.V, m)
        G = LeanHowardGraph(self.n, self.starts, self.V, self.W, m)
        mu, cyc = G.solve()
        del G, m
        return Fr(int(self.W[cyc].astype(np.int64).sum()), len(cyc))


def init_digs(A):
    """min_range.init_sums(A) is np.tile(digs, #shapes): the m1-periodic table digs."""
    t = np.arange(A.m1, dtype=np.int64)
    return sum((t // A.ns ** j) % A.ns + 1 for j in range(A.k - 1)).astype(np.int32)


def bf(G, p, q, pi0, max_iter, neg_check):
    """Jacobi Bellman-Ford from pi0 (int32, overwritten).  Returns pi or None (value < 0 / cap)."""
    lib = _load()
    nw = np.empty(G.n, np.int32); chg = np.empty(G.n, np.uint8); it = np.zeros(1, np.int64)
    r = lib.bf_jacobi(G.n, G.starts, G.V, G.W, int(p), int(q), pi0, nw, chg, int(max_iter), int(neg_check), it)
    del nw, chg
    bf.iters = int(it[0])
    if r == -3:
        raise OverflowError('int32 potential overflow')
    return pi0 if r == 0 else None


def bellman_ford(G, p, q, max_iter=100000):
    """refine_fast.bellman_ford on the CSR arrays (int32)."""
    return bf(G, p, q, np.zeros(G.n, np.int32), max_iter, 0)


def min_start_potential(A, G, p, q, hi, max_iter=4000, verbose=False):
    """min_range.min_start_potential: the same binary search over D and the same Jacobi iteration,
    returning (D, pi int32) or (None, None)."""
    lib = _load()
    digs = init_digs(A)
    lo, best = -q * int(digs.max()), None
    dmin = int(digs.min())
    while lo <= hi:
        mid = (lo + hi) // 2
        t0 = time.time()
        if mid + q * dmin < 0:                 # some ub < 0: bf_bounded fails at once (or all < 0: skipped)
            lo = mid + 1; continue
        pi = np.empty(G.n, np.int32)
        for s in range(len(A.shapes)):
            pi[s * A.m1:(s + 1) * A.m1] = mid + q * digs
        pi = bf(G, p, q, pi, max_iter, 1)
        ok = pi is not None and lib.check_pot(G.n, G.starts, G.V, G.W, int(p), int(q), pi, 1, int(mid),
                                              digs, A.m1) == 0
        if verbose:
            print(f'  start potential D={mid}: {"feasible" if ok else "infeasible"} '
                  f'({bf.iters} iterations, {time.time() - t0:.1f}s)', flush=True)
        if ok:
            best = (mid, pi); hi = mid - 1
        else:
            lo = mid + 1
        pi = None
    return best if best else (None, None)


def start_constant(A, pi, q):
    """max(pi - q * init) without n-sized int64 temporaries."""
    digs = init_digs(A).astype(np.int64)
    return max(int((pi[s * A.m1:(s + 1) * A.m1].astype(np.int64) - q * digs).max()) for s in range(len(A.shapes)))


def vertex_bound(A, G, vmax=260):
    """refine_fast.vertex_bound on the CSR arrays (int32 dynamic programme, INT32_MAX = inf)."""
    lib = _load()
    INF = np.iinfo(np.int32).max
    t0 = A.L - 1
    pre = t0 - (A.k - 1)
    digs = init_digs(A)
    dp = np.empty(G.n, np.int32)
    for s in range(len(A.shapes)):
        dp[s * A.m1:(s + 1) * A.m1] = digs
    dmin = int(dp.min()); out = np.empty(G.n, np.int32)
    best = None; steps = 0
    for v in range(t0 + 2, vmax + 1):
        n = v - 2
        while steps < n - t0:
            dmin = int(lib.dp_step(G.n, G.starts, G.V, G.W, dp, out))
            dp, out = out, dp; steps += 1
        if dmin != INF and 8 + pre + dmin <= 9214 - 35 * v:
            best = v
    return best


# ---- blockers ----------------------------------------------------------------------------------
class LeanBlockers:
    """minimize_fast.Blockers with count tables per (window shape, centres) instead of per extension."""

    def __init__(self, A, keys, c0):
        self.A, self.c0 = A, c0
        k, ns = A.k, A.ns
        self.by = BlockMap(A).by                                # (shape, cc) -> {ext: {'f', 'r'}}
        self.sym = {}
        for g, d in self.by.items():
            both = [o == {'f', 'r'} for o in d.values()]
            assert all(both) or not any(both), g               # a shape is palindromic or not, everywhere
            self.sym[g] = both[0]
        self.groups = {}                                        # (shape, cc) -> (exts int32, ori uint8)
        for g, d in self.by.items():
            es = sorted(d)
            self.groups[g] = (np.array(es, np.int32),
                              np.array([(1 if 'f' in d[e] else 0) | (2 if 'r' in d[e] else 0) for e in es], np.uint8))
        used = sorted({(x[0], len(x[1])) for x in keys if (x[0], len(x[1])) in self.by})
        self.off = {}
        tot = 0
        for g in used:
            self.off[g] = tot; tot += ns ** g[1]
        self.tab = np.zeros(max(tot, 1), np.int16)
        ne = len(A.ext)
        self.toff_f = np.full(ne * (k + 1), -1, np.int64); self.toff_r = np.full(ne * (k + 1), -1, np.int64)
        for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
            for cc, (fw, rv) in wins.items():
                self.toff_f[e * (k + 1) + cc] = self.off.get((fw, cc), -1)
                if rv != fw:
                    self.toff_r[e * (k + 1) + cc] = self.off.get((rv, cc), -1)
        self.revoff = np.zeros(k + 1, np.int64)
        rv = []; tot = 0
        for cc in range(k + 1):
            self.revoff[cc] = tot
            if cc >= 2:
                rv.append(A.rev[cc].astype(np.int32)); tot += len(A.rev[cc])
        self.rev = np.concatenate(rv)
        self.esrc = np.array([x[0] for x in A.ext], np.int32); self.enxt = np.array([x[2] for x in A.ext], np.int32)
        self.checked = np.zeros(1, np.int64)
        cnt = 0
        for x in keys:
            if self.relevant(x):
                self.tab[self._idx(x)] += 1; cnt += 1
        assert cnt < 32767 or int(self.tab.max()) < 32767
        print(f'  blocker tables: {len(used)} (shape, centres) groups, {self.tab.nbytes >> 20} MB', flush=True)

    def relevant(self, x):
        return (x[0], len(x[1])) in self.by

    def _idx(self, x):
        g = (x[0], len(x[1]))
        c = self.c0[x]
        if self.sym[g]:
            c = np.union1d(c, self.A.rev[g[1]][c])
        return self.off[g] + c

    def removable(self, x, pi, p, q):
        A = self.A
        g = (x[0], len(x[1]))
        exts, ori = self.groups[g]
        return bool(_load().removable(len(exts), exts, ori, len(self.c0[x]), self.c0[x], g[1], A.k, A.ns, A.m1,
                                      self.esrc, self.enxt, self.tab, self.toff_f, self.toff_r, self.rev,
                                      self.revoff, pi, int(p), int(q), self.checked))

    def remove(self, x):
        self.tab[self._idx(x)] -= 1


# ---- main --------------------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=5)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--avoid', help='JSON list of {dirs, alpha} windows never to keep (expensive certificates)')
    ap.add_argument('--tag', default='')
    ap.add_argument('--escalate', type=int, default=None, help='also use windows refuted only at this larger radius')
    ap.add_argument('--start', action='store_true',
                    help='keep what the start-bounded potential (smallest D = max(pi - Q * symbol sum)) needs')
    ap.add_argument('--prefer', help='certificate index: windows verified there are dropped last (they cost nothing)')
    ap.add_argument('--lam', help='keep only what a potential at this mean p/q needs (<= the minimum mean)')
    ap.add_argument('--out', help='output JSON path (default ../data/minimal_L{L}_k{k}_K{K}_r{radius}{tag}.json)')
    ap.add_argument('--vb-max-edges', type=int, default=None,
                    help='skip the exact walk bound (dp_bound_edges: null) above this many edges')
    a = ap.parse_args(argv)
    T0 = time.time()
    A = LeanAutomaton(a.L, a.k, a.K)
    if a.escalate:
        O = refine.TwoLevelOracle(a.radius, a.escalate)
    else:
        O = refine.Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            O.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    c0 = {}
    keys = []
    for x, st in O.known.items():
        if st == 'UNSAT' and 2 <= len(x[1]) <= a.k:
            c = sym_codes(x[1], A.ns, A.K)
            if len(c) > 0:
                keys.append(x); c0[x] = c
    by = BlockMap(A).by
    keep = {x for x in keys if (x[0], len(x[1])) in by}
    print('relevant exclusions', len(keep), flush=True)
    G = Graph(A, keep)
    print(f'  graph: {A.n} states, {G.E} edges ({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    lam = G.min_mean()
    if a.lam:
        target = Fr(a.lam)
        assert target <= lam, (target, lam)
        print('full set: minimum mean', lam, '; minimising for', target, flush=True)
        lam = target
    p, q = lam.numerator, lam.denominator
    if a.start:
        Dst, pi = min_start_potential(A, G, p, q, 300, verbose=True)
        assert pi is not None
        pi -= pi.min()
        Dst = start_constant(A, pi, q)
        print('full set: mean', lam, 'start constant D', Dst, 'range', int(pi.max()), flush=True)
    else:
        pi = bellman_ford(G, p, q); assert pi is not None
        print('full set: mean', lam, 'range', int(pi.max()) - int(pi.min()), flush=True)
    G = None
    print(f'  potential done ({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    Bk = LeanBlockers(A, keys, c0)
    certified = set()
    if a.prefer:
        certified = {(tuple(c['dirs']), tuple(map(tuple, c['alpha']))) for c in json.load(open(a.prefer))['cases']
                     if c.get('drat_trim_verified')}
        print('already certified among the relevant exclusions:', len(keep & certified), flush=True)
    order = sorted(keep, key=lambda x: (x in certified, -len(x[1]), -len(set(x[0]))))
    while True:
        t0 = time.time()
        dropped = 0
        for x in order:
            if x in keep and Bk.removable(x, pi, p, q):
                Bk.remove(x); keep.discard(x); dropped += 1
        if not a.start:
            G = Graph(A, keep)
            pi2 = bellman_ford(G, p, q); assert pi2 is not None
            pi = pi2
            G = None
        print('kept', len(keep), 'dropped', dropped, 'range', int(pi.max()) - int(pi.min()),
              f'({time.time() - t0:.0f}s, {int(Bk.checked[0])} codes checked)', flush=True)
        if dropped == 0:
            break
    print(f'  greedy done ({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    Bk = None
    G = Graph(A, keep)
    lam2 = G.min_mean(); assert lam2 >= lam, (lam, lam2)
    # the potential is still valid on the final graph (checked, not assumed)
    assert _load().check_pot(G.n, G.starts, G.V, G.W, p, q, pi - pi.min(), 0, 0, init_digs(A), A.m1) == 0
    if a.vb_max_edges is not None and G.E > a.vb_max_edges:
        vb = None
    else:
        t0 = time.time(); vb = vertex_bound(A, G)
        print(f'  walk bound {vb} ({time.time() - t0:.0f}s)', flush=True)
    R = int(pi.max()) - int(pi.min()); L = a.L
    C = p * L - q * (L - 1) + R
    if a.start:
        C = p * L - q * (L - a.k) + Dst
    Bp = (9179 * q + C - 8 * q) // (p + 35 * q)
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'min_mean': str(lam), 'potential_range': R,
           'potential_bound_edges': Bp, 'dp_bound_edges': None if vb is None else vb - 1, 'edges': int(G.E),
           'by_centres': dict(Counter(len(x[1]) for x in keep)),
           'already_certified': len(keep & certified),
           'exclusions': [{'dirs': list(x[0]), 'alpha': [list(r) for r in x[1]],
                           **({'radius': O.level(x)} if a.escalate else {})} for x in sorted(keep)]}
    path = a.out or os.path.join(DATA, f'minimal_L{a.L}_k{a.k}_K{a.K}_r{a.radius}{a.tag}.json')
    json.dump(out, open(path, 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'exclusions'}))
    print('wrote', path)
    print(f'total {time.time() - T0:.0f}s, peak RSS {rss_mb()} MB', flush=True)


if __name__ == '__main__':
    main()
