"""Direction (e): the level-T corner-share keys of milestone 38 as pseudo-Boolean problems.
Same CNF as milestone 38's AltShare (window, ball, e0/degree totalizers, shareCl clauses) except that
the final counter over the u literals is replaced by ONE native linear constraint  sum u <= T-1.
Solved with the Exact PB solver (cutting planes), cycle cuts added lazily.
usage: python3 pb_share.py 'DIRS' T timeout     (e.g. '[0,1,2,3,4,0,1,5]' 60 900)"""
import os, sys, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
for p in ('38-220-conditional/trackA', '28-combined-identities', '11-local-ceiling/s0_share_loop', '10-window-aggregate/scripts'):
    sys.path.insert(0, os.path.join(MS, p))
from enc2 import AltShare
from tier7 import ws, window_from_dirs
from wincert import cycles_of
import exact


class PBShare(AltShare):
    def build_share(self):
        self.mode = 'merge'
        self.tree = lambda xs, lim: [None]       # no counter, no shareCap clause
        AltShare.build_share(self)


def run(dirs, T, tl):
    w = window_from_dirs(list(dirs))
    t0 = time.time()
    enc = PBShare(w, ws.alpha_arg([(1, 21)] * 7), 4, 12, T - 1)
    assert 'shareCap' not in enc.kinds
    E = exact.Exact()
    for v in range(1, enc.nv + 1):
        E.addVariable(f"x{v}", 0, 1)
    def addcl(c):
        pos = [l for l in c if l > 0]; neg = [-l for l in c if l < 0]
        E.addConstraint([(1, f"x{l}") for l in pos] + [(-1, f"x{l}") for l in neg], True, 1 - len(neg))
    for c in enc.clauses:
        addcl(c)
    E.addConstraint([(1, f"x{u}") for u in enc.ulits], False, 0, True, T - 1)
    tb = time.time() - t0; cuts = 0
    while True:
        left = tl - (time.time() - t0)
        if left < 1:
            return dict(dirs=dirs, T=T, result='TIMEOUT', seconds=round(time.time() - t0, 1), build=round(tb, 1), cuts=cuts)
        r = E.runFull(False, left); print("runFull:", r, file=sys.stderr)
        if r == 'INCONSISTENT' or r == 'UNSAT':
            return dict(dirs=dirs, T=T, result='UNSAT', seconds=round(time.time() - t0, 1), build=round(tb, 1), cuts=cuts,
                        ulits=len(enc.ulits), vars=enc.nv, clauses=len(enc.clauses))
        if r != 'SAT':
            return dict(dirs=dirs, T=T, result=r, seconds=round(time.time() - t0, 1), build=round(tb, 1), cuts=cuts)
        vals = E.getLastSolutionFor([f"x{enc.var[v]}" for v in enc.ball])
        sel = [v for v, b in zip(enc.ball, vals) if b]
        cyc = cycles_of(sel)
        if not cyc:
            return dict(dirs=dirs, T=T, result='SAT', seconds=round(time.time() - t0, 1), cuts=cuts)
        for c in cyc:
            addcl([-enc.var[x] for x in c]); cuts += 1
        E.invalidateLastSol() if hasattr(E, 'invalidateLastSol') else None


if __name__ == '__main__':
    r = run(json.loads(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]))
    print(json.dumps(r), flush=True)
