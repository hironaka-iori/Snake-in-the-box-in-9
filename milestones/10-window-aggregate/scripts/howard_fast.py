"""Minimum cycle mean by Howard policy iteration in C (howard_c.c), with warm starts and
extraction of many near-minimal cycles.

The C routine follows the same evaluation and improvement rules as refine_fast.howard.  The
cycles returned are cycles of the input graph; their exact means are recomputed by the caller
from the integer weights, so the float arithmetic only steers the search.

    G = HowardGraph(n, U, V, W)
    mu, cyc = G.solve()                 # min mean (float) and its edges (input numbering)
    cycles = G.cycles(200, cap=mu + 0.3)  # list of (mean, edges): delete-and-resolve
"""
import ctypes, os, subprocess, time
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_SRC = os.path.join(HERE, 'howard_c.c')
_SO = os.path.join(HERE, 'howard_c.so')
_lib = None


def _load():
    global _lib
    if _lib is None:
        if not os.path.exists(_SO) or os.path.getmtime(_SO) < os.path.getmtime(_SRC):
            subprocess.check_call(['cc', '-O2', '-shared', '-fPIC', '-o', _SO, _SRC])
        lib = ctypes.CDLL(_SO)
        P = np.ctypeslib.ndpointer
        lib.howard_run.argtypes = [ctypes.c_int64, P(np.int64, flags='C'), P(np.int32, flags='C'),
                                   P(np.float64, flags='C'), P(np.uint8, flags='C'), P(np.int64, flags='C'),
                                   P(np.float64, flags='C'), P(np.float64, flags='C'), ctypes.c_int]
        lib.howard_run.restype = ctypes.c_int
        _lib = lib
    return _lib


class HowardGraph:
    def __init__(self, n, U, V, W, prefer=None):
        """prefer: optional array of preferred successor nodes per node (warm start)."""
        self.n = int(n)
        self.order = np.argsort(U, kind='stable')
        Us = np.ascontiguousarray(U[self.order], dtype=np.int64)
        self.V = np.ascontiguousarray(V[self.order], dtype=np.int32)
        self.W = np.ascontiguousarray(W[self.order], dtype=np.float64)
        self.starts = np.ascontiguousarray(np.searchsorted(Us, np.arange(self.n + 1)), dtype=np.int64)
        self.alive = np.ones(len(Us), np.uint8)
        self.pol = np.full(self.n, -1, np.int64)
        if prefer is not None:
            hit = np.nonzero(self.V == prefer[Us])[0]
            if len(hit):
                u_hit = Us[hit]
                first = np.unique(u_hit, return_index=True)
                self.pol[first[0]] = hit[first[1]]
        self.eta = np.empty(self.n); self.val = np.empty(self.n)
        self.iters = 0

    def solve(self, iters=10000):
        self.iters = _load().howard_run(self.n, self.starts, self.V, self.W, self.alive, self.pol,
                                        self.eta, self.val, iters)
        fin = np.isfinite(self.eta)
        if not fin.any():
            return None, []
        u0 = int(np.argmin(np.where(fin, self.eta, np.inf)))
        mu = float(self.eta[u0])
        seen = {}; x = u0; seq = []
        while x not in seen:
            seen[x] = len(seq); seq.append(x); x = int(self.V[self.pol[x]])
        cyc_sorted = [int(self.pol[y]) for y in seq[seen[x]:]]
        return mu, [int(self.order[e]) for e in cyc_sorted]

    def successors(self):
        """Policy successor of every node (-1 if none), for warm-starting the next graph."""
        return np.where(self.pol >= 0, self.V[np.maximum(self.pol, 0)], -1).astype(np.int64)

    def cycles(self, count, cap, budget=None):
        """Up to `count` cycles with mean <= cap: solve, record, delete the cycle's edges, repeat."""
        inv = np.empty(len(self.order), np.int64); inv[self.order] = np.arange(len(self.order))
        out = []; t0 = time.time()
        saved_pol = self.pol.copy(); saved_alive = self.alive.copy()
        while len(out) < count:
            mu, cyc = self.solve()
            if mu is None or mu > cap or not cyc:
                break
            out.append((mu, cyc))
            self.alive[inv[np.array(cyc)]] = 0
            if budget is not None and time.time() - t0 > budget:
                break
        self.pol = saved_pol; self.alive = saved_alive
        return out


def min_cycle(n, U, V, W):
    """Drop-in replacement for refine_fast.howard: (min mean as float, cycle edges in input numbering)."""
    return HowardGraph(n, U, V, W).solve()
