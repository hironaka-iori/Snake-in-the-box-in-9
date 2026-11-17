"""Uniform corner-share (shareN 12) minimum over 7-centre windows (8 directions), counts free.

For each of the 132 eight-direction shapes of the K7R34C7W16 chain, find the largest T such that
"the 7 centres have corner share sum <= T-1" is UNSAT (bisection between a SAT witness and UNSAT).
A uniform T >= 30 on every shape would give m <= 230 with the K7 chain and the corner identity
24 sum(alpha) + sum(share) + 840 (m+1) <= 221136.
usage: corner7.py SHAPES.jsonl OUT.jsonl [tl] [workers]
"""
import os, sys, json, time
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..'))
sys.path.insert(0, os.path.join(MS, '28-combined-identities'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
import share7, wincert_share as ws
from wincert import window_from_dirs

FREE = (1, 21)


def test(dirs, T, tl):
    w = window_from_dirs(list(dirs))
    k = len(w) - 2
    enc = share7.SubShareEncoding(w, ws.alpha_arg([FREE] * k), 4, 12, T - 1, range(1, k + 1))
    st, sel, cuts, sec = ws.solve(enc, tl)
    wit = ws.share_exact(w, sel) if sel else None
    return st, wit, round(sec, 1)


def one(args):
    dirs, tl = args
    lo, hi, log = 0, None, []          # lo: proved share >= lo; hi: witness share value
    T = 30
    while True:
        st, wit, sec = test(dirs, T, tl)
        log.append((T, st, wit, sec))
        if st == 'UNSAT':
            lo = T
            if hi is not None and hi <= lo:
                break
            T = T + 6 if hi is None else (lo + hi + 1) // 2
            if hi is not None and T > hi:
                break
        elif st == 'SAT':
            hi = wit if hi is None else min(hi, wit)
            if hi <= lo + 0:
                break
            T = (lo + hi + 1) // 2 if lo else max(1, min(T - 6, hi))
            if T <= lo:
                break
        else:
            break
        if len(log) > 10 or (hi is not None and T >= hi + 1):
            break
    return dict(dirs=list(dirs), lb=lo, witness=hi, log=log)


if __name__ == '__main__':
    shapes = [json.loads(l)['dirs'] for l in open(sys.argv[1])]
    out = sys.argv[2]; tl = float(sys.argv[3]) if len(sys.argv) > 3 else 120
    nw = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    done = set()
    if os.path.exists(out):
        done = {tuple(json.loads(l)['dirs']) for l in open(out)}
    todo = [(d, tl) for d in shapes if tuple(d) not in done]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo):
            with open(out, 'a') as f:
                f.write(json.dumps(r) + '\n')
            print(r['dirs'], r['lb'], r['witness'], flush=True)
