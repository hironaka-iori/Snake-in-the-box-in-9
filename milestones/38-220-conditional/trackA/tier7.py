"""Count-tiered corner-share floors of 7-centre windows (track A, milestone 38).

"every 8-direction window whose 7 centre counts all lie in [lo, hi] has corner share (M = 12) >= T":
the CNF is share7.SubShareEncoding over all 7 centres with alpha bounds [(lo, hi)] * 7, radius 4, cap T - 1
(the statement RefutedShare (winOf dirs) [(lo, hi)] x 7 12 (T - 1) of the Lean local model).
usage: tier7.py SHAPES.jsonl OUT.jsonl LO HI T [tl] [workers] [first] [count]
Records: dirs, lo, hi, T, result (UNSAT / SAT / TIMEOUT), witness share of a SAT model, seconds.
"""
import os, sys, json
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '28-combined-identities'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
import share7, wincert_share as ws
from wincert import window_from_dirs


def test(dirs, bounds, T, tl):
    w = window_from_dirs(list(dirs))
    k = len(w) - 2
    enc = share7.SubShareEncoding(w, ws.alpha_arg([tuple(b) for b in bounds]), 4, 12, T - 1, range(1, k + 1))
    st, sel, cuts, sec = ws.solve(enc, tl)
    wit = ws.share_exact(w, sel) if sel else None
    return st, wit, round(sec, 1), sel


def one(a):
    d, lo, hi, T, tl = a
    st, wit, sec, sel = test(d, [(lo, hi)] * 7, T, tl)
    r = dict(dirs=d, lo=lo, hi=hi, T=T, result=st, witness=wit, seconds=sec)
    if sel:
        r['sel'] = sorted(sel)
    return r


if __name__ == '__main__':
    shapes = [json.loads(l)['dirs'] for l in open(sys.argv[1])]
    out, lo, hi, T = sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    tl = float(sys.argv[6]) if len(sys.argv) > 6 else 300
    nw = int(sys.argv[7]) if len(sys.argv) > 7 else 2
    first = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    count = int(sys.argv[9]) if len(sys.argv) > 9 else len(shapes)
    done = set()
    if os.path.exists(out):
        done = {(tuple(r['dirs']), r['lo'], r['hi'], r['T']) for r in map(json.loads, open(out))}
    todo = [(d, lo, hi, T, tl) for d in shapes[first:first + count] if (tuple(d), lo, hi, T) not in done]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f:
                f.write(json.dumps(r) + '\n')
            print({k: v for k, v in r.items() if k != 'sel'}, flush=True)
