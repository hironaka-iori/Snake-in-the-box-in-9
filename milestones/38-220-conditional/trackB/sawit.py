"""Annealed witnesses (upper bounds) for window minima of W = sum (wA alpha + share_M), checked
against the radius-R window CNF (wincert.Encoding, counts free): the witness is a model of the
plain local model, so 'W <= value' is SAT.  usage: sawit.py DIRS R M wA iters seeds"""
import sys, json, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from combined import exact, ws, window_from_dirs
import wincert
from pysat.solvers import Cadical153

def run(dirs, R=4, M=12, wA=24, iters=400000, seed=1):
    w = window_from_dirs(list(dirs))
    inp = f"{len(w)} {' '.join(map(str, w))} {R} {M} {wA} {iters} {seed} 0\n"
    out = subprocess.run([os.path.join(HERE, 'sa')], input=inp, capture_output=True, text=True).stdout.split('\n')
    best = int(out[0]); sel = list(map(int, out[1].split()))
    return w, best, sel

def check(w, sel, R=4):
    enc = wincert.Encoding(w, [None] * (len(w) - 2), R)
    enc.build() if not enc.clauses else None
    S = set(sel)
    assum = [enc.var[v] if v in S else -enc.var[v] for v in enc.ball]
    with Cadical153(bootstrap_with=enc.clauses) as s:
        ok = s.solve(assumptions=assum)
    return ok and not wincert.cycles_of(sel)

if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); R = int(sys.argv[2]); M = int(sys.argv[3]); wA = int(sys.argv[4])
    iters = int(sys.argv[5]); seeds = int(sys.argv[6])
    bestr = None
    for sd in range(1, seeds + 1):
        w, b, sel = run(dirs, R, M, wA, iters, sd)
        A, SH = exact(w, sel, M)
        val = wA * sum(A) + sum(SH)
        ok = check(w, sel, R)
        r = dict(dirs=dirs, R=R, M=M, wA=wA, seed=sd, sa=b, value=val, alpha=A, share=SH, valid=ok, sel=sel)
        if ok and (bestr is None or val < bestr['value']):
            bestr = r
        print(json.dumps({k: r[k] for k in r if k != 'sel'}), flush=True)
    print('BEST', json.dumps(bestr))
