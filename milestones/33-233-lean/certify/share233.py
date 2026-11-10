"""The static-cap share CNF of a share threshold, with the meanings and tags of the Lean checker.

`TaggedShare` is main's `milestones/28-direct-share-certificates/scripts/tagged_share.py`
(origin/main at 32d14f72, git blob 8a6f27d8f3227a5223552328a655748cd0168a3a; the encoding of the
certified share floors 7300/7304/7306 of main's milestone 73), with three changes only:

* the base window CNF is this branch's `gen_lean_sat.TaggedEncoding` with the lumped bounds in the
  alpha form of `wincert` (an int for a fixed count, `(lo, hi)` otherwise);
* `add_cut` appends a lazy cycle cut (tag `('old', ('cut',))`), as `wincert.decide` does;
* `solve` is the lazy-cut solve of `milestones/11-local-ceiling/s0_share_loop/wincert_share.solve`.

The CNF is `wincert_share.ShareEncoding` up to the variable numbering: per centre `c = window[i]`
and non-path direction `kk`, `q = c ^ 2^kk`, the 28 empty-square variables (`emptyE`), the
upward totalizer over them (`totUp`), the downward totalizer over the 9 primaries of the
neighbours of `q` (`totDown`), the thresholds `u q t` for `t = 1 .. min(cap + 1, 12 * 28)`
(`shareCl`), and finally the cap totalizer over all thresholds, truncated at `cap + 1`, with the
unit `[-o_{cap+1}]` (`shareCap`).  UNSAT proves `RefutedShare (winOf ds) (boundsOf syms) 12 cap`
(`Tags.refutedShare_of_sat`), i.e. a share sum of at least `cap + 1` on the five centres.
"""
import itertools, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(ROOT, 'milestones', '10-window-aggregate', 'scripts'))
from gen_lean_sat import TaggedEncoding          # noqa: E402
from wincert import window_from_dirs, cycles_of  # noqa: E402
from pysat.solvers import Cadical153             # noqa: E402


class TaggedShare:
    def __init__(self, dirs, bounds, cap, M=12):
        self.window = window_from_dirs(list(dirs)); self.bounds = [tuple(b) for b in bounds]
        self.cap = cap; self.M = M
        alpha = [b[0] if b[0] == b[1] else tuple(b) for b in self.bounds]
        base = TaggedEncoding(self.window, alpha, radius=4)
        self.nv = base.nv; self.meaning = base.meaning; self.smeaning = {}; self.ctrs = base.ctrs
        self.clauses = base.clauses; self.tags = [('old', t) for t in base.tags]; self.var = base.var
        self.ball = base.ball
        self.tots = []; spec = []; ulits = []
        for ci, c in enumerate(self.window[1:-1], 1):
            used = {(c ^ self.window[ci - 1]).bit_length() - 1, (c ^ self.window[ci + 1]).bit_length() - 1}
            cs = []
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ (1 << kk); es = []
                for a, b in itertools.combinations(range(9), 2):
                    if kk in (a, b):
                        continue
                    e = self.fresh(('sq', q, a, b)); es.append(e)
                    self.add([self.var[v] for v in (q, q ^ (1 << a), q ^ (1 << b), q ^ (1 << a) ^ (1 << b))] + [e],
                             ('emptyE',))
                et, ge = self.totalizer(es, ('emp', q), up=True)
                dt, gd = self.totalizer([self.var[q ^ (1 << a)] for a in range(9)], ('nb', q), up=False, down=True)
                tmax = min(cap + 1, M * len(es)); cs.append((kk, tmax))
                for t in range(1, tmax + 1):
                    u = self.fresh(('u', q, t)); ulits.append(u)
                    for d in range(1, 10):
                        need = (t * d + M - 1) // M
                        if need > len(es):
                            continue
                        clause = [u, -ge[need]]
                        if d < 9:
                            clause.append(gd[d + 1])
                        self.add(clause, ('shareCl', et, dt))
            spec.append(cs)
        ti, out = self.totalizer(ulits, ('cap', spec), up=True, limit=cap + 1)
        self.add([-out[cap + 1]], ('shareCap', ti))
        self.nbase = len(self.clauses)

    def fresh(self, meaning):
        self.nv += 1; self.smeaning[self.nv] = meaning; return self.nv

    def add(self, clause, tag):
        self.clauses.append(clause); self.tags.append(tag)

    def add_cut(self, cyc):
        self.add([-self.var[v] for v in cyc], ('old', ('cut',)))

    def totalizer(self, lits, kind, up, down=False, limit=None):
        ti = len(self.tots); self.tots.append((lits, kind)); limit = len(lits) if limit is None else limit

        def rec(lo, hi):
            if hi - lo == 1:
                return [None, lits[lo]]
            mid = (lo + hi) // 2; a = rec(lo, mid); b = rec(mid, hi); na = len(a) - 1; nb = len(b) - 1
            out = [None] + [self.fresh(('t', ti, lo, hi, c)) for c in range(1, min(hi - lo, limit) + 1)]
            for i in range(na + 1):
                for j in range(nb + 1):
                    if up and 0 < i + j < len(out):
                        self.add([out[i + j]] + ([-a[i]] if i else []) + ([-b[j]] if j else []), ('totUp', ti))
                    if down and i + j + 1 < len(out):
                        self.add([-out[i + j + 1]] + ([a[i + 1]] if i < na else []) + ([b[j + 1]] if j < nb else []),
                                 ('totDown', ti))
            return out
        return ti, rec(0, len(lits))


def solve(enc, time_limit=3600.0, budget=20000):
    """Lazy-cut solve of the static clause set: ('UNSAT' | 'SAT' | 'TIMEOUT', cuts as vertex lists,
    seconds).  The cuts are appended to `enc` (tag `('old', ('cut',))`)."""
    t0 = time.time(); cuts = []
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while True:
            if time.time() - t0 > time_limit:
                return 'TIMEOUT', cuts, time.time() - t0
            s.conf_budget(budget)
            ok = s.solve_limited()
            if ok is None:
                continue
            if not ok:
                return 'UNSAT', cuts, time.time() - t0
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', cuts, time.time() - t0
            for c in cyc:
                enc.add_cut(c); cuts.append(list(c))
                s.add_clause(enc.clauses[-1])
