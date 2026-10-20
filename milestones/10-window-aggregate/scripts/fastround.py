"""Faster refinement rounds for refine_fast --lean (copy next to lean_automaton.py).

1. IncrementalLean: keep the LeanAutomaton edge arrays across rounds.  A window refuted since the
   last build only removes edges (UNSAT is permanent; AVOID / UNKNOWN never block), so the round's
   graph is the previous prune mask with the newly blocked edges cleared, re-pruned in place
   (prune_masked, C).  blocked_edges(keys) maps window keys to edge ids with the same rule as
   FastAutomaton.forb_tables/_mask: a key (dirs, alpha) with c = len(alpha) centres blocks, in every
   extension whose length-c window has forward shape dirs, the codes whose low c digits are in
   sym_codes(alpha), and where the reversed shape is dirs, the reversed codes rev[c][sym_codes].

2. Many near-minimal cycles from ONE Howard solve on the full graph.  With eta, val from the solve,
   every alive edge u->v inside an eta class has reduced cost rc = W - eta[u] + val[v] - val[u] >= 0,
   every cycle lies in one class and has mean eta + (sum rc) / length (fastround_c.c).
   rc_cycles: delete-and-resolve (the same rule as LeanHowardGraph.cycles) but on the compact
   subgraph of edges with rc <= R, pruned to its cycles: near-minimal cycles use few, small positive
   rc edges, and that subgraph is ~10x smaller (L7 k6 K7: 0.75M of 8.9M edges at R = 0.5), so each
   re-solve is ~10x cheaper.  tight_cycles: a cheaper but weaker depth-first walk through the low-rc
   edges.  Exact means are recomputed from the integer weights; cycles above the cap are dropped.
"""
import ctypes, os, subprocess, sys, time
from fractions import Fraction as Fr
import numpy as np

SCRIPTS = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts'
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)
from minimize_fast import sym_codes                      # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
_lib = None


def _load():
    global _lib
    if _lib is None:
        src = os.path.join(HERE, 'fastround_c.c'); so = os.path.join(HERE, 'fastround_c.so')
        if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(src):
            subprocess.check_call(['cc', '-O2', '-shared', '-fPIC', '-o', so, src])
        lib = ctypes.CDLL(so)
        P = np.ctypeslib.ndpointer
        i64, f64 = ctypes.c_int64, ctypes.c_double
        lib.prune_masked.argtypes = [i64, P(np.int64, flags='C'), P(np.int32, flags='C'), P(np.uint8, flags='C')]
        lib.prune_masked.restype = ctypes.c_int
        lib.tight_cycles.argtypes = [i64, P(np.int64, flags='C'), P(np.int32, flags='C'), P(np.uint8, flags='C'),
                                     P(np.uint8, flags='C'), P(np.float64, flags='C'), P(np.float64, flags='C'),
                                     f64, f64, f64, ctypes.c_int, i64, i64, i64, i64,
                                     P(np.int64, flags='C'), P(np.int64, flags='C')]
        lib.tight_cycles.restype = ctypes.c_int64
        lib.rc_select.argtypes = [i64, P(np.int64, flags='C'), P(np.int32, flags='C'), P(np.uint8, flags='C'),
                                  P(np.uint8, flags='C'), P(np.float64, flags='C'), P(np.float64, flags='C'),
                                  f64, f64, P(np.uint8, flags='C')]
        lib.rc_select.restype = ctypes.c_int64
        lib.compact_subgraph.argtypes = [i64, P(np.int64, flags='C'), P(np.int32, flags='C'), P(np.uint8, flags='C'),
                                         P(np.uint8, flags='C'), P(np.int32, flags='C'), P(np.int64, flags='C'),
                                         P(np.int32, flags='C'), P(np.uint8, flags='C'), P(np.int32, flags='C')]
        lib.compact_subgraph.restype = ctypes.c_int64
        _lib = lib
    return _lib


def prune_masked(n, starts, V, m):
    """In place: m (bool or uint8 edge mask) := refine_fast.prune of the edges with m set."""
    mu8 = m.view(np.uint8) if m.dtype == bool else m
    return _load().prune_masked(int(n), starts, V, mu8)


def unsat_keys(oracle):
    """The keys forb_tables reads as exclusions."""
    return {x for x, st in oracle.known.items() if st == 'UNSAT'}


class BlockMap:
    """Window key -> CSR edge ids it forbids, for a LeanAutomaton whose arrays are built."""

    def __init__(self, A):
        self.A = A
        self.by = {}                                     # (shape, centres) -> {ext: orientations}
        for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
            for cc, (fw, rv) in wins.items():
                self.by.setdefault((fw, cc), {}).setdefault(e, set()).add('f')
                self.by.setdefault((rv, cc), {}).setdefault(e, set()).add('r')

    def candidates(self, x):
        """(ext, k-digit code array) pairs blocked by key x, whether or not the edge still exists."""
        A = self.A
        dirs, alpha = x
        cc = len(alpha)
        if cc < 2 or cc > A.k or (dirs, cc) not in self.by:
            return []
        c0 = sym_codes(alpha, A.ns, A.K)
        if len(c0) == 0:
            return []
        js = np.arange(A.ns ** (A.k - cc), dtype=np.int64) * A.ns ** cc
        out = []
        for e, ori in self.by[(dirs, cc)].items():
            low = [c0] if 'f' in ori else []
            if 'r' in ori:
                low.append(A.rev[cc][c0])
            low = np.unique(np.concatenate(low))
            out.append((e, (low[:, None] + js[None, :]).ravel()))
        return out

    def blocked_edges(self, keys, starts, EXT, W, chunk=1 << 22):
        """Sorted unique edge ids (in the built arrays) of edges blocked by any of `keys`."""
        A = self.A
        ns, m1 = A.ns, A.m1
        maxdeg = int(np.diff(starts).max()) if len(starts) > 1 else 0
        steps = max(1, int(maxdeg).bit_length() + 1)
        pend_u, pend_t, size, found = [], [], 0, []

        def flush():
            nonlocal pend_u, pend_t, size
            if not pend_u:
                return
            u = np.concatenate(pend_u); t = np.concatenate(pend_t)
            pend_u, pend_t, size = [], [], 0
            lo = starts[u].copy(); hi = starts[u + 1].copy()
            for _ in range(steps):                       # lower_bound of t in the segment's (ext, w) keys
                act = lo < hi
                if not act.any():
                    break
                mid = (lo + hi) >> 1
                km = EXT[np.minimum(mid, len(EXT) - 1)].astype(np.int64) * ns + W[np.minimum(mid, len(W) - 1)] - 1
                less = act & (km < t)
                lo = np.where(less, mid + 1, lo)
                hi = np.where(act & ~less, mid, hi)
            ok = lo < starts[u + 1]
            lo, t = lo[ok], t[ok]
            hit = (EXT[lo].astype(np.int64) * ns + W[lo] - 1) == t
            found.append(lo[hit])

        for x in keys:
            for e, codes in self.candidates(x):
                i = A.ext[e][0]
                pend_u.append(i * m1 + codes // ns)
                pend_t.append(e * ns + codes % ns)
                size += len(codes)
                if size >= chunk:
                    flush()
        flush()
        return np.unique(np.concatenate(found)) if found else np.zeros(0, np.int64)


class IncrementalLean:
    """Holds one LeanAutomaton build (U, V, W, EXT, starts) and its prune mask m across rounds."""

    def __init__(self, A, U, V, W, EXT, m, built_keys):
        self.A, self.U, self.V, self.W, self.EXT, self.m = A, U, V, W, EXT, m
        self.starts = A.starts
        self.built = set(built_keys)
        self.bmap = BlockMap(A)

    def update(self, oracle):
        """Clear the edges of windows refuted since the last update and re-prune.  Returns
        (newly refuted key count, blocked edge ids) or None if an exclusion disappeared (rebuild)."""
        cur = unsat_keys(oracle)
        if not self.built <= cur:
            return None
        new = cur - self.built
        ids = self.bmap.blocked_edges(new, self.starts, self.EXT, self.W) if new else np.zeros(0, np.int64)
        if len(ids):
            mu8 = self.m.view(np.uint8) if self.m.dtype == bool else self.m
            had = mu8[ids].any()
            mu8[ids] = 0
            if had:
                prune_masked(self.A.n, self.starts, self.V, self.m)
        self.built = cur
        return len(new), ids


def tight_cycles(G, count, cap, eps=4.0, exclude=(), max_len=48, max_depth=None, max_out=1 << 22, raw=10,
                 levels=6):
    """Up to `count` edge-disjoint cycles with exact mean <= cap from the current solve of the
    LeanHowardGraph G (call right after G.solve()), by the depth-first reduced-cost walk of
    fastround_c.c.  Returns [(Fraction mean, edge list)], ascending by (mean, length).
    `exclude`: edges kept out of the search (cycles already found).  eps: largest reduced cost of a
    single edge the walk may take; `levels` passes with f = 0, 1/2^(levels-2), ..., 1 allow edges with
    rc <= f eps and keep cycles with mean <= mu + f (cap - mu); up to raw * count cycles are collected
    and the best `count` by exact mean are returned.  max_len: longest cycle kept; max_depth: deepest
    walk (default 8 max_len)."""
    fin = np.isfinite(G.eta)
    if not fin.any():
        return []
    mu0 = float(G.eta[fin].min())
    max_depth = max_depth or 8 * max_len
    ex = np.asarray(list(exclude), np.int64)
    saved = G.alive[ex].copy(); G.alive[ex] = 0
    try:
        out_edges = np.empty(max_out, np.int64); out_off = np.zeros(raw * count + 1, np.int64)
        nc = _load().tight_cycles(G.n, G.starts, G.V, G.W, G.alive, G.eta, G.val, mu0, float(cap), float(eps),
                                  int(levels), raw * count, int(max_len), int(max_depth), int(max_out),
                                  out_edges, out_off)
    finally:
        G.alive[ex] = saved
    res = []
    for c in range(nc):
        cyc = out_edges[out_off[c]:out_off[c + 1]]
        mean = Fr(int(G.W[cyc].astype(np.int64).sum()), len(cyc))
        if float(mean) <= cap + 1e-9:
            res.append((mean, [int(e) for e in cyc]))
    res.sort(key=lambda t: (t[0], len(t[1])))
    return res[:count]


def resolve_cycles(G, count, cap, budget=None):
    """LeanHowardGraph.cycles (solve, record, delete the cycle's edges, repeat) with one fix: after each
    deletion the alive mask is re-pruned (prune_masked).  Without it, deleting a cycle can leave states
    with no alive out-edge; when every warm-started policy path runs into one of them, the C Howard sees
    no policy cycle, every eta stays inf, no improvement exists and solve() returns None although
    cycles of mean <= cap remain (L8 k7 K3 snapshot: G.cycles stops after 46 cycles, a cold solve of the
    same graph still has mean 5/2).  alive and pol are restored before returning."""
    out = []; t0 = time.time()
    saved_pol = G.pol.copy(); saved_alive = G.alive.copy()
    try:
        while len(out) < count:
            mu, cyc = G.solve()
            if mu is None or mu > cap or not cyc:
                break
            out.append((mu, cyc))
            G.alive[np.asarray(cyc, np.int64)] = 0
            prune_masked(G.n, G.starts, G.V, G.alive)
            if budget is not None and time.time() - t0 > budget:
                break
    finally:
        G.alive[:] = saved_alive                       # in place: G.alive may share the caller's mask
        G.pol = saved_pol
    return out


def rc_subgraph(G, cap, R, exclude=(), max_edges=None):
    """Compact LeanHowardGraph on the edges of G with reduced cost <= R inside an eta class <= cap,
    minus `exclude`, pruned to its cycles; warm-started from G's policy.  Returns (H, idx) with idx[j] =
    G's edge number of H's edge j (int32), (None, None) if no cycle is left, or ('big', count) if more
    than max_edges edges are selected (before pruning).  Memory: 1 B per edge of G, 4 B per state of G,
    ~9 B per selected edge."""
    from lean_automaton import LeanHowardGraph
    lib = _load()
    sel = np.empty(len(G.V), np.uint8)
    cnt = lib.rc_select(G.n, G.starts, G.V, G.W, G.alive, G.eta, G.val, float(cap), float(R), sel)
    if max_edges is not None and cnt > max_edges:
        return 'big', int(cnt)
    sel[np.asarray(list(exclude), np.int64)] = 0
    prune_masked(G.n, G.starts, G.V, sel)
    nsel = int(sel.sum())
    if not nsel:
        return None, None
    smap = np.empty(G.n, np.int32)
    starts = np.empty(G.n + 1, np.int64)               # trimmed below
    Vs = np.empty(nsel, np.int32); Ws = np.empty(nsel, np.uint8); idx = np.empty(nsel, np.int32)
    ns = lib.compact_subgraph(G.n, G.starts, G.V, G.W, sel, smap, starts, Vs, Ws, idx)
    del sel
    starts = starts[:ns + 1].copy()
    succ = G.successors()                              # warm start: G's policy successors, compacted
    states = np.flatnonzero(smap >= 0)
    sv = succ[states]
    pref = np.where(sv >= 0, smap[np.maximum(sv, 0)], -1).astype(np.int64)
    del smap, succ, states, sv
    H = LeanHowardGraph(int(ns), starts, Vs, Ws, np.ones(nsel, np.uint8), prefer=pref)
    return H, idx


def rc_cycles(G, count, cap, R=0.5, budget=None, exclude=(), max_R=4.0, max_edges=40_000_000, verbose=False):
    """Near-minimal cycles from one solve of G: delete-and-resolve (resolve_cycles) on the
    reduced-cost subgraph rc <= R, which is much smaller than G, so each re-solve is cheap.  When the
    subgraph has no cycle of mean <= cap left, R doubles (up to max_R) and the search goes on in the
    larger subgraph without the cycles found so far, until `count` cycles or the budget (seconds), or
    until the subgraph would have more than max_edges edges (memory: ~9 B per subgraph edge).
    Every cycle returned is a cycle of G with exact mean <= cap, edge-disjoint from the others and
    from `exclude`.  Returns [(Fraction mean, edge list in G numbering)] ascending by (mean, length)."""
    t0 = time.time()
    out, used = [], [int(e) for e in exclude]
    while len(out) < count and R <= max_R + 1e-9:
        if budget is not None and time.time() - t0 > budget:
            break
        t1 = time.time()
        H, idx = rc_subgraph(G, cap, R, used, max_edges=max_edges)
        if isinstance(H, str):
            if verbose:
                print(f'  rc-subgraph R={R}: {idx} edges > max_edges, stop', flush=True)
            break
        found = []
        if H is not None:
            rest = None if budget is None else max(0.0, budget - (time.time() - t0))
            found = resolve_cycles(H, count - len(out), cap, budget=rest)
            for _, c in found:
                cg = [int(idx[e]) for e in c]
                mean = Fr(int(G.W[cg].astype(np.int64).sum()), len(cg))
                if float(mean) <= cap + 1e-9:
                    out.append((mean, cg))
                used.extend(cg)
        if verbose:
            print(f'  rc-subgraph R={R}: {0 if H is None else len(idx)} edges, {0 if H is None else H.n} states, '
                  f'{len(found)} cycles ({time.time() - t1:.1f}s)', flush=True)
        H = idx = None
        R *= 2
    out.sort(key=lambda t: (t[0], len(t[1])))
    return out
