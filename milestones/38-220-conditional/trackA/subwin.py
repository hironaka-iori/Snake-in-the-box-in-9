"""Uniform corner-share floors of short windows (k = 1..6 centres, counts free) and what they give for the
7-centre keys by additivity (track A, milestone 38).

The share of a 7-centre window is the sum of the shares of the sub-windows of any split of its centres into
consecutive blocks, so  floor7(s) >= max over splits of sum of floors of the block shapes.  A block of k
centres is a (k+1)-direction window: 1, 1, 2, 4, 12, 34 canonical shapes for k = 1..6.
For each short shape: bisection on T ("share <= T - 1" UNSAT / SAT with the exact share of the model),
production encoding (share7.SubShareEncoding, radius 4, M = 12), `tl` seconds per query.
usage: subwin.py OUT.jsonl kmax tl workers"""
import sys, json, os
from multiprocessing import Pool
import tier7


def canon(ds):
    m = {}
    return tuple(m.setdefault(d, len(m)) for d in ds)


def shapes(k):
    S = set()
    for l in open(os.path.join(tier7.MS, '37-230-feasibility', 'data', 'k7_shapes_parallel_X26.jsonl')):
        d = json.loads(l)['dirs']
        for i in range(0, 8 - k):
            S.add(canon(d[i:i + k + 1]))
    return sorted(S)


def one(a):
    dirs, tl = a
    k = len(dirs) - 1
    lo, hi, tmo, log = 0, None, None, []     # share >= lo proved; hi = share of a model; tmo = lowest level that timed out
    T = 4 * k
    while len(log) < 14:
        st, wit, sec, sel = tier7.test(list(dirs), [(1, 21)] * k, T, tl)
        log.append([T, st, wit, round(sec, 1)])
        if st == 'UNSAT':
            lo = T
        elif st == 'SAT':
            hi = wit if hi is None else min(hi, wit)
        else:
            tmo = T if tmo is None else min(tmo, T)
        top = min(x for x in (hi + 1 if hi is not None else None, tmo) if x is not None) if (hi is not None or tmo is not None) else None
        if top is None:
            T = 2 * T
        elif top - lo <= 1:
            break
        else:
            T = (lo + top) // 2
    return dict(dirs=list(dirs), k=k, lb=lo, witness=hi, timeout_at=tmo, log=log)


if __name__ == '__main__':
    out, kmax, tl, nw = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    done = {tuple(json.loads(l)['dirs']) for l in open(out)} if os.path.exists(out) else set()
    todo = [(s, tl) for k in range(1, kmax + 1) for s in shapes(k) if s not in done]
    with Pool(nw) as p:
        for r in p.imap_unordered(one, todo, 1):
            open(out, 'a').write(json.dumps(r) + '\n')
            print(r['dirs'], 'lb', r['lb'], 'wit', r['witness'], [(x[0], x[1][0], x[3]) for x in r['log']], flush=True)
