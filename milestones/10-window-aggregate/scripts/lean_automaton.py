"""Memory-lean drop-in for refine_fast.FastAutomaton.

LeanAutomaton(L, k, K).edges(oracle) returns the same allowed edge set as
FastAutomaton.edges, as (U int32, V int32, W uint8, EXT int16), sorted by source
(CSR order: source, then extension, then new symbol).  self.starts (int64, n+1)
holds the CSR offsets.  Built per shape into preallocated arrays: 11 bytes per
edge plus small per-shape temporaries (a packed bitmask of 1/8 byte per
candidate edge lives until the fill is done).

decode / window_key are inherited unchanged (EXT indexes self.ext exactly as in
FastAutomaton).  refine_fast.prune works on these arrays but makes int64
temporaries (~16 B/edge); prune_lean is the chunked equivalent (1 B/edge result).
LeanHowardGraph runs the C Howard on the CSR arrays in place (uint8 weights,
alive = prune mask), so edge numbers it returns are numbers in U/V/W/EXT.

Weighted edges (share_lb.py): after A.set_weights(den, ShareTable), W is uint16 =
den * symbol + LB units of the k-centre window ending at the new vertex; den = 1 with no LB keeps uint8
and reproduces the unweighted arrays bit for bit.  The symbol of edge e is always A.sym(V[e]) =
V[e] % ns + 1 (the low digit of the target's count state), so decode / BlockMap no longer read W.

NOTE: W is uint8 (or uint16).  refine_fast.bellman_ford computes q*W - p, which under
numpy 2 promotion stays uint8 and wraps; pass W.astype(np.int64) there.
"""
import ctypes, itertools, os, subprocess, sys, time
import numpy as np

SCRIPTS = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts'
if SCRIPTS not in sys.path:
    sys.path.append(SCRIPTS)                            # patched copies next to this file win
from refine import canon, induced                      # noqa: E402
from refine_fast import FastAutomaton                    # noqa: E402
from share_lb import lookup as _lookup                   # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))


def fast_shapes(L):
    """Canonical induced direction shapes of length L (same list as FastAutomaton's, sorted)."""
    out = []

    def rec(ds, m):
        if not induced(tuple(ds)):
            return
        if len(ds) == L:
            out.append(tuple(ds)); return
        for d in range(min(m + 1, 9)):
            rec(ds + [d], max(m, d + 1))
    rec([], 0)
    return sorted(out)


class LeanAutomaton(FastAutomaton):
    den = 1
    lbx = {}

    def set_weights(self, den=1, table=None):
        """Edge weight den * symbol + LB units (share_lb.ShareTable); den = 1, no table: unweighted."""
        self.den = int(den)
        self.lbx = table.ext_tables(self, self.den) if table is not None else {}
        return self

    @property
    def weighted(self):
        return self.den != 1 or bool(self.lbx)

    def wdtype(self):
        return np.uint16 if self.weighted else np.uint8

    def sym(self, v):
        """New symbol of an edge from its target state (works for any weights)."""
        return v % self.ns + 1

    def edge_weights(self, e_arr, codes):
        """Weights of edges (extension e_arr, k-digit code) -- den * symbol + LB units."""
        w = self.den * (codes % self.ns + 1)
        if self.lbx:
            w = w.astype(np.int64)
            for e in np.unique(e_arr):
                tab = self.lbx.get(int(e))
                if tab is not None:
                    sel = e_arr == e
                    w[sel] += _lookup(tab, codes[sel])
        return w

    def __init__(self, L, k, K, slow_init=False):
        if slow_init:
            FastAutomaton.__init__(self, L, k, K)
            return
        assert L >= k
        self.L, self.k, self.K = L, k, K
        self.ns = K + 1
        self.shapes = fast_shapes(L)
        self.sid = {c: i for i, c in enumerate(self.shapes)}
        self.m1 = self.ns ** (k - 1)
        self.n = len(self.shapes) * self.m1
        self.ext = []
        for i, c in enumerate(self.shapes):
            for d in range(min(max(c) + 2, 9)):
                ds = c + (d,)
                if not induced(ds):
                    continue
                nxt = self.sid[canon(ds[1:])]
                wins = {cc: (canon(ds[-(cc + 1):]), canon(tuple(reversed(ds[-(cc + 1):]))))
                        for cc in range(2, k + 1)}
                self.ext.append((i, d, nxt, ds, wins))
        # reversed-tuple code per window length (vectorised; FastAutomaton builds it in Python)
        self.rev = {}
        for cc in range(2, k + 1):
            x = np.arange(self.ns ** cc, dtype=np.int64)
            r = np.zeros_like(x)
            for j in range(cc):
                r = r * self.ns + (x // self.ns ** j) % self.ns
            self.rev[cc] = r
        # self.codes (int64 over ns^k) is only used by FastAutomaton.edges; not allocated here

    # ---- allowed-symbol masks -------------------------------------------------------------
    def _mask(self, wins, T, out):
        """out (bool, ns^k) := allowed codes for one extension; broadcast, no index temporaries."""
        ns, k = self.ns, self.k
        out[:] = True
        for cc, (fw, rv) in wins.items():
            view = out.reshape(ns ** (k - cc), ns ** cc)        # low cc digits = last cc symbols
            if fw in T:
                view &= ~T[fw][None, :]
            if rv in T:
                view &= ~T[rv][self.rev[cc]][None, :]
        return out

    def edges(self, oracle, block_cells=1 << 21, verbose=False, count_only=False):
        """count_only: run pass 1 only and return (edge count, CSR starts) -- memory ~ states + 1/8 B per candidate."""
        t0 = time.time()
        T = self.forb_tables(oracle)
        ns, k, m1 = self.ns, self.k, self.m1
        nc = ns ** k
        by_shape = {}
        for e, (i, d, nxt, ds, wins) in enumerate(self.ext):
            by_shape.setdefault(i, []).append(e)
        # pass 1: masks per shape -> packed bits, out-degree per state
        packed = {}
        deg = np.zeros(self.n, np.int64)
        buf = np.empty(nc, bool)
        for i, es in by_shape.items():
            M = np.empty((len(es), nc), bool)
            for j, e in enumerate(es):
                self._mask(self.ext[e][4], T, M[j])
            deg[i * m1:(i + 1) * m1] = M.reshape(len(es), m1, ns).sum(axis=(0, 2))
            packed[i] = np.packbits(M)
            del M
        starts = np.zeros(self.n + 1, np.int64)
        np.cumsum(deg, out=starts[1:])
        del deg
        E = int(starts[-1])
        if verbose:
            print(f'  lean pass 1: {E} edges, packed {sum(p.nbytes for p in packed.values()) >> 20} MB, '
                  f'{time.time() - t0:.1f}s', flush=True)
        if count_only:
            return E, starts
        U = np.empty(E, np.int32); V = np.empty(E, np.int32)
        W = np.empty(E, self.wdtype()); EXT = np.empty(E, np.int16)
        assert len(self.ext) < 2 ** 15 and self.n < 2 ** 31 and ns < 256
        # pass 2: fill in (source, extension, symbol) order
        for i, es in by_shape.items():
            nE = len(es)
            M = np.unpackbits(packed.pop(i), count=nE * nc).view(bool).reshape(nE, m1, ns)
            nxt = np.array([self.ext[e][2] for e in es], np.int64)
            rows = max(1, block_cells // (nE * ns))
            for t0_ in range(0, m1, rows):
                t1_ = min(m1, t0_ + rows)
                f = np.flatnonzero(np.ascontiguousarray(M[:, t0_:t1_, :].transpose(1, 0, 2)))
                a = int(starts[i * m1 + t0_]); b = a + len(f)
                assert b == starts[i * m1 + t1_]
                t, r = np.divmod(f, nE * ns)
                j, w = np.divmod(r, ns)
                t += t0_
                U[a:b] = i * m1 + t
                V[a:b] = nxt[j] * m1 + (t * ns + w) % m1
                if self.weighted:
                    W[a:b] = self.edge_weights(j + es[0], t * ns + w)
                else:
                    W[a:b] = w + 1
                EXT[a:b] = j + es[0]
            del M
        self.starts = starts
        if verbose:
            print(f'  lean pass 2: done {time.time() - t0:.1f}s', flush=True)
        assert all(es == list(range(es[0], es[0] + len(es))) for es in by_shape.values())
        return U, V, W, EXT


# ---- chunked prune on the CSR arrays -----------------------------------------------------------
def _blocks(starts, max_edges=1 << 23):
    """State ranges [a, b) whose edge ranges have at most ~max_edges edges."""
    n = len(starts) - 1
    cuts = np.searchsorted(starts, np.arange(0, int(starts[-1]), max_edges), side='right') - 1
    cuts = np.unique(np.concatenate([[0], np.clip(cuts, 0, n), [n]]))
    return list(zip(cuts[:-1].tolist(), cuts[1:].tolist()))


def prune_lean(n, starts, V, blocks=None):
    """Same result as refine_fast.prune(n, U, V) (bool mask of edges between surviving states);
    temporaries are per block.  U is not needed: sources come from the CSR offsets."""
    blocks = blocks or _blocks(starts)
    alive = np.ones(n, bool)
    m = np.empty(len(V), bool)
    while True:
        out = np.zeros(n, bool); inn = np.zeros(n, bool)
        for a, b in blocks:
            e0, e1 = int(starts[a]), int(starts[b])
            if e0 == e1:
                continue
            Uc = np.repeat(np.arange(a, b, dtype=np.int32), np.diff(starts[a:b + 1]))
            Vc = V[e0:e1]
            mc = alive[Uc]
            mc &= alive[Vc]
            m[e0:e1] = mc
            out[a:b] |= np.bincount(Uc[mc] - a, minlength=b - a) > 0
            inn[Vc[mc]] = True
        new = alive & out & inn
        if (new == alive).all():
            return m
        alive = new


class IdentityIndex:
    """Stands in for idx = np.nonzero(m)[0] when the Howard graph keeps the full numbering."""
    def __init__(self, count):
        self.count = int(count)

    def __getitem__(self, e):
        return e

    def __len__(self):
        return self.count


# ---- Howard on the CSR arrays in place ------------------------------------------------------
_lib = None


def _load():
    global _lib
    if _lib is None:
        src = os.path.join(HERE, 'howard_lean.c'); so = os.path.join(HERE, 'howard_lean.so')
        if not os.path.exists(src):                     # copied next to a howard_c.c patched with howard_c_u8.patch
            src = os.path.join(HERE, 'howard_c.c'); so = os.path.join(HERE, 'howard_c.so')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.check_call(['cc', '-O2', '-shared', '-fPIC', '-o', so, src])
        lib = ctypes.CDLL(so)
        P = np.ctypeslib.ndpointer
        lib.howard_run_u8.argtypes = [ctypes.c_int64, P(np.int64, flags='C'), P(np.int32, flags='C'),
                                      P(np.uint8, flags='C'), P(np.uint8, flags='C'), P(np.int64, flags='C'),
                                      P(np.float64, flags='C'), P(np.float64, flags='C'), ctypes.c_int]
        lib.howard_run_u8.restype = ctypes.c_int
        at16 = list(lib.howard_run_u8.argtypes); at16[3] = P(np.uint16, flags='C')
        lib.howard_run_u16.argtypes = at16
        lib.howard_run_u16.restype = ctypes.c_int
        _lib = lib
    return _lib


class LeanHowardGraph:
    """howard_fast.HowardGraph without copies: the graph is already in CSR order (LeanAutomaton.edges),
    W stays uint8, and the prune mask is the alive array (shared, not copied; restored after
    cycles()).  Edge numbers returned are indices into the LeanAutomaton arrays."""

    def __init__(self, n, starts, V, W, alive, prefer=None, blocks=None):
        self.n = int(n)
        self.starts, self.V, self.W = starts, V, W
        assert V.dtype == np.int32 and W.dtype in (np.uint8, np.uint16) and starts.dtype == np.int64
        self.alive = alive.view(np.uint8) if alive.dtype == bool else alive
        self.pol = np.full(self.n, -1, np.int64)
        if prefer is not None:
            for a, b in (blocks or _blocks(starts)):
                e0, e1 = int(starts[a]), int(starts[b])
                if e0 == e1:
                    continue
                Uc = np.repeat(np.arange(a, b, dtype=np.int64), np.diff(starts[a:b + 1]))
                hit = np.nonzero((V[e0:e1] == prefer[Uc]) & (self.alive[e0:e1] != 0))[0]
                if len(hit):
                    u, first = np.unique(Uc[hit], return_index=True)
                    self.pol[u] = e0 + hit[first]
        self.eta = np.empty(self.n); self.val = np.empty(self.n)
        self.iters = 0

    def solve(self, iters=10000):
        run = _load().howard_run_u16 if self.W.dtype == np.uint16 else _load().howard_run_u8
        self.iters = run(self.n, self.starts, self.V, self.W, self.alive, self.pol,
                                           self.eta, self.val, iters)
        fin = np.isfinite(self.eta)
        if not fin.any():
            return None, []
        u0 = int(np.argmin(np.where(fin, self.eta, np.inf)))
        mu = float(self.eta[u0])
        seen = {}; x = u0; seq = []
        while x not in seen:
            seen[x] = len(seq); seq.append(x); x = int(self.V[self.pol[x]])
        return mu, [int(self.pol[y]) for y in seq[seen[x]:]]

    def successors(self):
        return np.where(self.pol >= 0, self.V[np.maximum(self.pol, 0)], -1).astype(np.int64)

    def cycles(self, count, cap, budget=None):
        out = []; t0 = time.time()
        saved_pol = self.pol.copy(); deleted = []
        try:
            while len(out) < count:
                mu, cyc = self.solve()
                if mu is None or mu > cap or not cyc:
                    break
                out.append((mu, cyc))
                c = np.array(cyc, np.int64)
                deleted.append(c); self.alive[c] = 0
                if budget is not None and time.time() - t0 > budget:
                    break
        finally:
            for c in deleted:                     # cycle edges were alive before deletion
                self.alive[c] = 1
            self.pol = saved_pol
        return out
