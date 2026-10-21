"""Alpha-conditioned 2- and 3-centre windows: ascending threshold ladder per key, one incremental
solver per direction shape (same encoding and soundness argument as sweep_w3.py).

Every key (shape, alpha symbols in 1..5 or 6+) climbs T = c * level for level in LADDER,
starting above its single-centre floor, until a test is SAT (witness = ub) or times out.
The proved lbs feed refine_w3.Sub.floor5 (DP over sub-windows of the five-centre keys).
usage: sub_sweep.py --c 3 --minutes 40 [--tl 4]
"""
import argparse, itertools, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
import w3survey as survey
from w3survey import solve_assume, key, shapes
import refine_w3 as R
from sweep_w3 import AlphaInc
from pysat.solvers import Cadical153

LADDER = list(range(262, 320, 3))
SYMS = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 21)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--c', type=int, default=3)
    ap.add_argument('--minutes', type=float, default=40)
    ap.add_argument('--tl', type=float, default=4)
    a = ap.parse_args()
    t_end = time.time() + a.minutes * 60
    sub = R.Sub(); O = R.W3Oracle()
    c = a.c
    for ds in shapes(c):
        keys = sorted({key(ds, al) for al in itertools.product(SYMS, repeat=c)})
        keys = [k for k in keys if k[0] == ds]
        enc = AlphaInc(w3enc.window_from_dirs(list(ds)), None, 4, c * 330)
        print(f'shape {ds}: {len(keys)} keys, {len(enc.clauses)} clauses', flush=True)
        stats = dict(steps=0, sat=0, timeout=0)
        with Cadical153(bootstrap_with=enc.clauses) as sv, open(R.ORACLE, 'a') as f:
            for k in keys:
                floor = sum(sub.single_lb(x) for x in k[1])
                s = O.get(k)
                lb = max(floor, s['lb'])
                for L in LADDER:
                    T = c * L
                    if T <= lb:
                        continue
                    if time.time() > t_end or T >= s['ub'] or T >= s['fail']:
                        break
                    st, sel, cuts, sec = solve_assume(sv, enc, enc.assumptions(k[1], T), a.tl)
                    wv = w3enc.window_charge(enc.window, sel) if sel else None
                    r = dict(dirs=list(k[0]), alpha=[list(x) for x in k[1]], T=T, result=st, witness=wv,
                             cuts=cuts, seconds=round(sec, 2), kind='subsweep')
                    f.write(json.dumps(r) + '\n'); f.flush(); O.apply(r)
                    stats['steps'] += 1
                    if st != 'UNSAT':
                        stats['sat' if st == 'SAT' else 'timeout'] += 1
                        break
                s = O.get(k)
                print(f'  {k[1]}: lb {max(s["lb"], floor)} ub {s["ub"] if s["ub"] < R.INF else None}', flush=True)
        print(f'done {ds}: {stats}', flush=True)
        if time.time() > t_end:
            break


if __name__ == '__main__':
    main()
