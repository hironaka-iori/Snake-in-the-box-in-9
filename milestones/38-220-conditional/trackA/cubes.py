"""Per-centre share cubes of a level-T key (track A): sum of 7 centre shares <= T - 1 implies some centre has
share <= (T - 1) // 7, so the 7 cubes "centre c has share <= k" (unit -cen[c][k + 1] in the merge encoding,
together with the full cap) cover the key.  usage: cubes.py OUT.jsonl 'DIRS' T tl [opts...]"""
import sys, json
from multiprocessing import Pool
import tier7, binsolve
from enc2 import AltShare
from tier7 import ws, window_from_dirs


def one(a):
    dirs, T, tl, c, opts = a
    w = window_from_dirs(list(dirs))
    enc = AltShare(w, ws.alpha_arg([(1, 21)] * 7), 4, 12, T - 1, 'merge', True, 1)
    k = (T - 1) // 7
    st, sec, cuts, confl = binsolve.solve(enc, opts, tl, extra=[[-enc.cen[c][k + 1]]])
    return dict(dirs=dirs, T=T, centre=c, k=k, opts=opts, result=st, seconds=round(sec, 1), cuts=cuts, conflicts=confl)


if __name__ == '__main__':
    out, dirs, T, tl = sys.argv[1], json.loads(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    with Pool(4) as p:
        for r in p.imap_unordered(one, [(dirs, T, tl, c, sys.argv[5:]) for c in range(1, 8)]):
            open(out, 'a').write(json.dumps(r) + '\n'); print(r, flush=True)
