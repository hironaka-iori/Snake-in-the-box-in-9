"""Threshold-SAT encoding of "the window's 3-cube charge is at most K" (radius-4 windows).

Charge.  For a vertex set S and x in S let
    c(x) = sum over the 84 3-subcubes Q containing x of h(|Q cap S|),   h(n) = floor(12/n),
so h = 12, 6, 4, 3, 2 for n = 1..5 (a 3-cube meets a snake in at most 5 vertices).
Since n h(n) <= 12, double counting gives the global census
    sum_{x in S} c(x) = sum_{Q nonempty} |Q cap S| h(|Q cap S|) <= 12 N_3 = 12 * 5376 = 64512,
and c(x) <= 12 w_3(x), with equality unless some 3-cube through x has 5 snake vertices
(h(5) = 2 < 12/5).  c is the integer form of w_3 used here (units: 12 c-units = 1 w_3).

Encoding.  W3Encoding(window, alpha, radius, cap) is wincert.Encoding (unchanged clauses, built
first; alpha entries may be None = unconstrained) followed by, for every centre c and every
3-subset t of coordinates (cube Q = c + span(t), other corners o_1..o_7, r = #selected o's):
    totDown   downward totalizer g over the 7 others  (g[j] -> at least j of them selected)
    cubeY     y_j  or  g[j+1]      for the levels j = 3, 2, 1, 0 that can occur
              (y_j is forced whenever r <= j; levels j < #path directions in t are skipped,
               because r >= #path directions in t holds in the model: the path neighbours
               are window vertices)
and the weighted sum  sum_Q (y_3 + y_2 + 2 y_1 + 6 y_0)  (literals repeated by weight; this is
h(1+r) - 2) in one upward totalizer truncated at cap' + 1, with the unit  -o[cap' + 1],
cap' = cap - 168 k  (168 = 84 * h(5) per centre).
In every configuration of the local model the forced y's give exactly sum h - 168 k, so UNSAT of
the static CNF (with the lazily found cycle cuts) proves  sum_{centres} c >= cap + 1.
"""
import itertools, os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
import wincert
from wincert import window_from_dirs, cycles_of
from pysat.solvers import Cadical153

H = {1: 12, 2: 6, 3: 4, 4: 3, 5: 2}
WEIGHTS = {3: 1, 2: 1, 1: 2, 0: 6}          # y_j weight; h(1+r) - 2 = sum_{j >= r} WEIGHTS[j]
BASE = 84 * 2


def cube_pts(c, t):
    pts = [c]
    for d in t:
        pts += [p ^ 1 << d for p in pts]
    return pts


def path_dirs(window, i):
    c = window[i]
    return {(c ^ window[i - 1]).bit_length() - 1, (c ^ window[i + 1]).bit_length() - 1}


def charge(sel, x):
    """c(x) = sum_Q floor(12 / |Q cap S|) over the 84 3-cubes through x."""
    S = set(sel)
    return sum(H[sum(1 for p in cube_pts(x, t) if p in S)] for t in itertools.combinations(range(9), 3))


def w3_60(sel, x):
    """60 w_3(x) (exact)."""
    S = set(sel)
    return sum(60 // sum(1 for p in cube_pts(x, t) if p in S) for t in itertools.combinations(range(9), 3))


class W3Encoding(wincert.Encoding):
    def __init__(self, window, alpha=None, radius=4, cap=None, ends=2):
        self.cap = cap
        if alpha is None:
            alpha = [None] * (len(window) - 2)
        super().__init__(window, alpha, radius, ends)

    def build(self):
        super().build()
        self.nbase_clauses, self.nbase_vars = len(self.clauses), self.nv
        if self.cap is not None:
            self.build_w3()

    def totalizer(self, lits, up=True, down=False, limit=None, kind_up='totUp', kind_down='totDown'):
        lim = limit if limit is not None else len(lits)

        def rec(ls):
            if len(ls) == 1:
                return [None, ls[0]]
            a = rec(ls[:len(ls) // 2]); b = rec(ls[len(ls) // 2:])
            na, nb = len(a) - 1, len(b) - 1
            no = min(na + nb, lim)
            o = [None] + [self.fresh() for _ in range(no)]
            for i in range(na + 1):
                for j in range(nb + 1):
                    if up and 0 < i + j <= no:
                        c = [o[i + j]]
                        if i: c.append(-a[i])
                        if j: c.append(-b[j])
                        self.add(c, kind_up)
                    if down and i + j + 1 <= no:
                        c = [-o[i + j + 1]]
                        if i + 1 <= na: c.append(a[i + 1])
                        if j + 1 <= nb: c.append(b[j + 1])
                        self.add(c, kind_down)
            return o
        return rec(list(lits))

    def build_w3(self):
        X, B, w = self.var, self.B, self.window
        k = len(w) - 2
        self.cubes, wl = [], []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = path_dirs(w, ci)
            for t in itertools.combinations(range(9), 3):
                pts = cube_pts(c, t)
                assert all(p in B for p in pts), 'radius too small'
                others = [X[p] for p in pts[1:]]
                npath = len(used & set(t))
                g = self.totalizer(others, up=False, down=True)
                ys = {}
                for j in (3, 2, 1, 0):
                    if j < npath:
                        continue
                    y = self.fresh(); ys[j] = y
                    self.add([y, g[j + 1]], 'cubeY')
                    wl += [y] * WEIGHTS[j]
                self.cubes.append(dict(c=ci, t=t, y=ys))
        capp = self.cap - BASE * k
        self.capp = capp
        if capp < 0:
            self.add([], 'w3Cap')            # trivially UNSAT: impossible threshold
            return
        if capp < len(wl):
            o = self.totalizer(wl, up=True, limit=capp + 1)
            self.add([-o[capp + 1]], 'w3Cap')


def window_charge(window, sel):
    return sum(charge(sel, window[i]) for i in range(1, len(window) - 1))


def solve(enc, time_limit=60.0, budget=20000):
    """Lazy-cut solve.  Returns (status, selection, cuts, seconds); status UNSAT / SAT / TIMEOUT."""
    t0 = time.time(); cuts = 0
    if any(len(c) == 0 for c in enc.clauses):
        return 'UNSAT', None, 0, 0.0
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while True:
            if time.time() - t0 > time_limit:
                return 'TIMEOUT', None, cuts, time.time() - t0
            s.conf_budget(budget)
            ok = s.solve_limited()
            if ok is None:
                continue
            if not ok:
                return 'UNSAT', None, cuts, time.time() - t0
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', sel, cuts, time.time() - t0
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
                s.add_clause(enc.clauses[-1])


FSIZE_KB = 120 * 1024      # proof files capped at 120 MB (disk budget)
CADICAL = os.environ.get('CADICAL', '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical')


def measure_proof(enc, workdir, timeout=900):
    """Cold CaDiCaL --lrat solve of the static CNF (with its cuts), trimmed to the empty clause's
    dependencies; every proof file is deleted right after it is measured."""
    sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
    from gen_lean_core import trim_lrat
    os.makedirs(workdir, exist_ok=True)
    cnf = os.path.join(workdir, 'm.cnf'); raw = os.path.join(workdir, 'm.raw.lrat')
    trimmed = os.path.join(workdir, 'm.lrat')
    wincert.write_cnf(enc, cnf)
    out = {'variables': enc.nv, 'clauses': len(enc.clauses), 'cnf_bytes': os.path.getsize(cnf)}
    try:
        t = time.time()
        r = subprocess.run(['bash', '-c', f'ulimit -f {FSIZE_KB}; exec nice -n 19 {CADICAL} -q --lrat --no-binary {cnf} {raw}'],
                           capture_output=True, text=True, timeout=timeout)
        out['lrat_seconds'] = round(time.time() - t, 1)
        out['lrat_raw_bytes'] = os.path.getsize(raw) if os.path.exists(raw) else 0
        if r.returncode != 20:
            out['failed'] = 'lrat run rc %d (file cap?)' % r.returncode
            return out
        nl, nh, core = trim_lrat(raw, trimmed, len(enc.clauses))
        os.remove(raw)
        out.update(lrat_lemmas=nl, lrat_hints=nh, core_clauses=len(core), lrat_trim_bytes=os.path.getsize(trimmed))
    except subprocess.TimeoutExpired:
        out['timeout'] = True
    finally:
        for p in (cnf, raw, trimmed):
            if os.path.exists(p):
                os.remove(p)
    return out
