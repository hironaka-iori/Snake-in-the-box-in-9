"""Adaptive count split of a uniform corner-share floor (track A, milestone 38).

Goal: "every 7-centre window of shape DIRS has corner share >= T" as a tree of count boxes, each leaf a
RefutedShare (winOf DIRS) box 12 (T - 1) that CaDiCaL proves within `tl` seconds.  A box that times out is
split on one centre: an interval [lo, hi] with lo <= 4 < hi into [lo, 4] and [5, hi], otherwise into
[lo, lo] and [lo + 1, hi]; the centre is the one with the widest interval (middle centres first).
A box of exact counts that still times out is recorded as HARD (and retried with `tl_hard`).
usage: split7.py 'DIRS(json)' T OUT.jsonl [tl] [tl_hard] [workers] [max_seconds]
Records: box, result, seconds, depth; the last line is a summary (leaves, total solver seconds, hard boxes, SAT)."""
import sys, json, time
from concurrent.futures import ProcessPoolExecutor, FIRST_COMPLETED, wait
import tier7
ORDER = [3, 2, 4, 1, 5, 0, 6]


def run(a):
    dirs, box, T, tl = a
    st, wit, sec, sel = tier7.test(dirs, box, T, tl)
    return box, st, wit, sec


def split(box):
    w = max(hi - lo for lo, hi in box)
    if w == 0:
        return None
    i = next(i for i in ORDER if box[i][1] - box[i][0] == w)
    lo, hi = box[i]
    cut = 4 if lo <= 4 < hi else lo
    a = list(box); b = list(box)
    a[i] = (lo, cut); b[i] = (cut + 1, hi)
    return [a, b]


if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); T = int(sys.argv[2]); out = sys.argv[3]
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 20
    tlh = float(sys.argv[5]) if len(sys.argv) > 5 else 120
    nw = int(sys.argv[6]) if len(sys.argv) > 6 else 4
    maxs = float(sys.argv[7]) if len(sys.argv) > 7 else 1800
    t0 = time.time()
    todo = [([(1, 21)] * 7, 0, tl)]
    stat = dict(dirs=dirs, T=T, tl=tl, leaves=0, unsat_seconds=0.0, timeout_seconds=0.0, nodes=0, hard=0, sat=0, open=0)
    with ProcessPoolExecutor(nw) as ex, open(out, 'a') as f:
        fut = {}
        while todo or fut:
            while todo and len(fut) < nw and time.time() - t0 < maxs:
                box, dep, lim = todo.pop()
                fut[ex.submit(run, (dirs, box, T, lim))] = (dep, lim)
            if not fut:
                break
            done, _ = wait(fut, return_when=FIRST_COMPLETED)
            for d in done:
                dep, lim = fut.pop(d)
                box, st, wit, sec = d.result()
                stat['nodes'] += 1
                f.write(json.dumps(dict(box=box, result=st, witness=wit, seconds=sec, depth=dep)) + '\n'); f.flush()
                if st == 'UNSAT':
                    stat['leaves'] += 1; stat['unsat_seconds'] += sec
                elif st == 'SAT':
                    stat['sat'] += 1
                else:
                    stat['timeout_seconds'] += sec
                    ch = split([tuple(x) for x in box])
                    if ch is None:
                        if lim < tlh:
                            todo.append((box, dep, tlh))
                        else:
                            stat['hard'] += 1
                    else:
                        todo += [(c, dep + 1, tl) for c in ch]
        stat['open'] = len(todo)
        stat['wall'] = round(time.time() - t0)
        f.write(json.dumps(dict(summary=stat)) + '\n')
    print(stat)
