"""Empty-square share lower bounds as automaton edge weights.

Accounting (v vertices, T = squares with one selected vertex = sum of all alpha(x) incl. endpoints,
s0 = empty squares;  T + 2 s0 = 9214 - 35 v):

  share(x) = omega(x) - 21 alpha(x) = sum_Q 6/m  (omega_oracle.OmegaModel), and
  sum_{internal x} share(x) <= 42 s0           (each empty Q gives <= 6 to each of its 7 parallel squares)
  =>  21 T + sum_x share(x) <= 21 (T + 2 s0) = 21 (9214 - 35 v).

Each automaton edge appends one internal vertex x_j; its window is the k-centre window W_j ending at x_j
(centres x_{j-k+1..j}, all internal; directions ds[-(k+1):], symbols al).  A certified LB(W) <= sum of the
shares of W's centres, and a vertex is a centre of at most k of the windows W_j, so

  sum_j LB(W_j) <= k sum_x share(x)  =>  21 k T + sum_j LB(W_j) <= 21 k (9214 - 35 v).

With DEN = 21 k the edge weight is w' = DEN * symbol + LB(W_j) (integer, uint16), and T is replaced by
T' = DEN * (8 + (L - k) + init) + sum_edges w' <= DEN (9214 - 35 v): endpoints (alpha >= 4) and the L - k
earliest internal vertices (alpha >= 1) keep weight DEN * count with no share credit, and the k - 1 counts
in the first state give DEN * init.  A smaller den is also sound with LB scaled down:
w' = den * symbol + floor(LB * den / (21 k)).

Potential bound at mean P/Q of w' (start potential 0 <= pi <= Dst + Q * den * init):
  max edges = (9179 Q den - 8 Q den + P L - Q den (L - k) + Dst) // (P + 35 Q den)
(den = 1: the existing (9179 Q + C - 8 Q) // (P + 35 Q), C = P L - Q (L - k) + Dst).
"""
import json, os, sys, time
import numpy as np

SCRIPTS = '/home/user/Snake-in-the-box-in-9/milestones/10-window-aggregate/scripts'
if SCRIPTS not in sys.path:
    sys.path.append(SCRIPTS)
from minimize_fast import sym_codes                      # noqa: E402

U16MAX = 65535


def unit(k):
    """The exact common denominator 21 k."""
    return 21 * k


def bound_edges(P, Q, L, k, Dst, den=1):
    """Largest edge count allowed by a start potential at mean P/Q (weights in 1/den alpha units)."""
    return (9179 * Q * den - 8 * Q * den + P * L - Q * den * (L - k) + Dst) // (P + 35 * Q * den)


def walk_ok(T_units, v, den=1):
    """Scaled accounting test of the walk dynamic programme: T' <= den (9214 - 35 v)."""
    return T_units <= den * (9214 - 35 * v)


def parse_key(e):
    return (tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))


class ShareTable:
    """Window key (canonical dirs, count ranges; refine.key form, k centres) -> certified share LB."""

    def __init__(self, lb=None):
        self.lb = dict(lb or {})

    @classmethod
    def load(cls, path, certified_only=False):
        t = cls()
        if path and os.path.exists(path):
            for line in open(path):
                line = line.strip()
                if not line:
                    continue
                e = json.loads(line)
                if certified_only and not e.get('certified'):
                    continue
                if e.get('lb') is None:
                    continue
                x = parse_key(e)
                t.lb[x] = max(t.lb.get(x, 0), int(e['lb']))
        return t

    def raise_(self, x, lb):
        if lb > self.lb.get(x, 0):
            self.lb[x] = int(lb); return True
        return False

    def ext_tables(self, A, den):
        """Per extension e: (sorted k-digit codes, LB in units) for the edges of e with LB > 0.
        Same orientation rule as FastAutomaton.forb_tables / _mask: a key (dirs, alpha) applies at the codes
        sym_codes(alpha) of extensions whose k-window forward shape is dirs, and at rev[k][codes] where the
        reversed shape is dirs (the same physical window read backwards: shares are reversal invariant)."""
        k, ns, K = A.k, A.ns, A.K
        U = unit(k)
        cap = U16MAX - den * ns
        byshape = {}
        for x, lb in self.lb.items():
            if len(x[1]) != k or lb <= 0:
                continue
            c = sym_codes(x[1], ns, K)
            if len(c) == 0:
                continue
            val = min(cap, (int(lb) * den) // U)
            if val <= 0:
                continue
            byshape.setdefault(x[0], []).append((c, np.full(len(c), val, np.int64)))
        tabs = {}
        for e, (i, d, nxt, ds, wins) in enumerate(A.ext):
            fw, rv = wins[k]
            parts = []
            for c, v in byshape.get(fw, []):
                parts.append((c, v))
            for c, v in byshape.get(rv, []):
                parts.append((A.rev[k][c], v))
            if not parts:
                continue
            cs = np.concatenate([p[0] for p in parts]); vs = np.concatenate([p[1] for p in parts])
            o = np.lexsort((-vs, cs))                      # by code, largest LB first
            cs, vs = cs[o], vs[o]
            first = np.ones(len(cs), bool); first[1:] = cs[1:] != cs[:-1]
            tabs[e] = (cs[first], vs[first])
        return tabs


def lookup(tab, codes):
    """LB units of the given codes under one extension table (0 where absent)."""
    cs, vs = tab
    pos = np.searchsorted(cs, codes)
    pos_c = np.minimum(pos, len(cs) - 1)
    hit = cs[pos_c] == codes
    return np.where(hit, vs[pos_c], 0)


def window_of_edge(A, u, e, sym):
    """refine.key of the k-centre window ending at the edge's new vertex."""
    ds, al = A.decode(u, e, sym)
    return A.window_key(tuple(ds[-(A.k + 1):]), tuple(al[-A.k:]))


# ---- LB oracle stub: CP-SAT minimum of the window's share sum ---------------------------------
def cpsat_share_lb(x, radius=3, time_limit=30.0):
    """Lower bound on sum_c (omega(c) - 21 alpha(c)) over the centres of window x, any local
    configuration (radius-`radius` ball, OmegaModel constraints, the window's count ranges), from CP-SAT's
    proven objective bound; induced-path cycle cuts are added lazily (each cut is valid for snakes, so the
    cut model is still a relaxation and its bound a valid LB).  Returns (lb, status, seconds).  Not a
    certificate: certifying LB means refuting 'shares <= LB - 1' (decshare.py) with a checked proof."""
    from omega_oracle import OmegaModel
    from wincert import cycles_of
    from ortools.sat.python import cp_model
    t = time.time()
    M = OmegaModel(list(x[0]), radius)
    M.constrain_alpha([tuple(a) for a in x[1]])
    M.m.Minimize(sum(M.omega[c] - 21 * M.alpha[c] for c in M.centers))
    s = cp_model.CpSolver(); s.parameters.num_workers = 1
    lb, status = 0, 'UNKNOWN'
    while True:
        rem = time_limit - (time.time() - t)
        if rem <= 0.5:
            break
        s.parameters.max_time_in_seconds = rem
        st = s.Solve(M.m)
        if st == cp_model.INFEASIBLE:          # window excluded outright: no edge carries it
            return None, 'INFEASIBLE', time.time() - t
        if st in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.UNKNOWN):
            b = s.BestObjectiveBound()
            if np.isfinite(b):
                lb = max(lb, int(np.ceil(b - 1e-6)))
        if st != cp_model.OPTIMAL:
            break
        sel = [v for v in M.ball if s.Value(M.X[v])]
        cy = cycles_of(sel)
        if not cy:
            status = 'OPTIMAL'; break
        for c in cy:
            M.m.AddBoolOr([M.X[w].Not() for w in c])
    return lb, status, time.time() - t


class LBOracle:
    """Cached CP-SAT share bounds (jsonl in this directory, never the repository's data)."""

    def __init__(self, path, radius=3, time_limit=30.0):
        self.path, self.radius, self.tl = path, radius, time_limit
        self.done = {}
        if os.path.exists(path):
            for line in open(path):
                e = json.loads(line)
                if e.get('radius') == radius:
                    self.done[parse_key(e)] = e.get('lb')

    def query(self, keys, table, max_new=None, verbose=True):
        """Ask the windows not asked yet; raise `table`.  Returns the keys whose LB rose."""
        new = [x for x in dict.fromkeys(keys) if x not in self.done]
        if max_new is not None:
            new = new[:max_new]
        risen = []
        with open(self.path, 'a') as f:
            for x in new:
                lb, st, sec = cpsat_share_lb(x, self.radius, self.tl)
                self.done[x] = lb
                f.write(json.dumps({'dirs': list(x[0]), 'alpha': [list(a) for a in x[1]], 'radius': self.radius,
                                    'lb': lb, 'status': st, 'seconds': round(sec, 1), 'certified': False}) + '\n')
                if verbose:
                    print(f'    share LB {x}: {lb} ({st}, {sec:.1f}s)', flush=True)
        for x in keys:
            lb = self.done.get(x)
            if lb and table.raise_(x, lb):
                risen.append(x)
        return risen
