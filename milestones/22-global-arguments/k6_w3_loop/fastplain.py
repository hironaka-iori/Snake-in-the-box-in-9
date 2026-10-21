"""Fast plain 6-window tests: one prebuilt base encoding per direction shape (wincert.Encoding with alpha
free + per-centre corner totalizers, sweep_w3.AlphaInc, no symmetry breaking), and per key a fresh CaDiCaL
on base + alpha units (the units of a key's alpha ranges on the totalizer outputs; equivalent to the
static key CNF up to these definitional totalizer clauses).  Lazy cycle cuts are kept in the shape's base
(they are valid for every key).  Checked against earlier statuses by control6.py --fast."""
import time
from k6w3loop import *
from sweep_w3 import AlphaInc
from pysat.solvers import Cadical153


class FastPlain:
    def __init__(self):
        self.base = {}

    def enc(self, ds):
        if ds not in self.base:
            self.base[ds] = AlphaInc(w3enc.window_from_dirs(list(ds)), None, 4, None, sym=False)
            if len(self.base) > 6:                       # memory: keep a few shapes
                self.base.pop(next(iter(self.base)))
        return self.base[ds]

    def solve(self, k, tl):
        e = self.enc(k[0])
        units = []
        for i, (lo, hi) in enumerate(k[1]):
            if lo >= 1:
                units.append([e.atot[i][lo]])
            if hi < 21:
                units.append([-e.atot[i][hi + 1]])
        t0 = time.time(); cuts = 0
        with Cadical153(bootstrap_with=e.clauses + units) as s:
            while True:
                if time.time() - t0 > tl:
                    return 'TIMEOUT', None, cuts, time.time() - t0
                s.conf_budget(20000)
                ok = s.solve_limited()
                if ok is None:
                    continue
                if not ok:
                    return 'UNSAT', None, cuts, time.time() - t0
                m = s.get_model()
                sel = [v for v in e.ball if m[e.var[v] - 1] > 0]
                cyc = w3enc.cycles_of(sel)
                if not cyc:
                    return 'SAT', sel, cuts, time.time() - t0
                for c in cyc:
                    e.add_cycle_cut(c); cuts += 1
                    s.add_clause(e.clauses[-1])
