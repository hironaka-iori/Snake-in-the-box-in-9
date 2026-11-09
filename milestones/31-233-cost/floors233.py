"""What main's Lean share floors save on a 233 set (step "reuse of main's share floors").

With the set's potential (fresh Bellman-Ford), a 5-window whose level is covered by a Lean floor
(share >= 16 on 012032/012031/012304/012314, 17 on the milestone-155 counts) is *used* when one of
its transitions is allowed and needs a positive level: Q 120 s - P + pi(u) - pi(v) < 0.  Without the
floors each used window would need its own RefutedShare certificate at the level it needs.  A random
sample of used windows is solved at that level (wincert_share, time limit 60 s) and costed with the
calibrated share model; the mean is extrapolated to all used windows.

usage: floors233.py TAG [SAMPLE]   -> data/floors_TAG.json
"""
import sys, os, json, random, time
import numpy as np
import lib233 as L
import steps233 as S


def main():
    tag = sys.argv[1]; ns = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    pq = tuple(json.load(open(os.path.join(L.D, f'sum_{tag}.json')))[x] for x in ('P', 'Q', 'B'))
    W = S.world(pq, tag)
    ok, it, rng = W.check(); assert ok
    crit, need, shcov = S.critical_state(W)
    allowed = W.cnt == 0
    g = np.flatnonzero(crit & allowed)
    ids = W.k5[g]
    fl = W.sF[ids] > 0
    used = {}
    for i, nd in zip(ids[fl], need[g][fl]):
        used[int(i)] = max(used.get(int(i), 0), int(nd))
    lv = {}
    for i, nd in used.items():
        lv[nd] = lv.get(nd, 0) + 1
    random.seed(31)
    sample = random.sample(sorted(used), min(ns, len(used)))
    rows = []; t0 = time.time()
    for i in sample:
        k = W.k5keys[i]; T = used[i]
        st, sec = S.decide_share(k, T, 60.0)
        h = L.share_hints(sec) if st == 'UNSAT' else None
        rows.append(dict(key=[list(k[0]), list(k[1])], T=T, result=st, seconds=round(sec, 2), hints=h))
        L.log(json.dumps(rows[-1]))
    hs = [r['hints'] for r in rows if r['hints'] is not None]
    mean = sum(hs) / len(hs) if hs else None
    out = dict(tag=tag, floor_windows_with_level=int((W.sF > 0).sum()), floor_windows_used=len(used),
               used_by_needed_level=dict(sorted(lv.items())), sample=len(rows),
               sample_unsat=len(hs), sample_mean_hints=mean,
               saved_hints_estimate=(mean * len(used)) if mean else None, seconds=round(time.time() - t0),
               rows=rows)
    json.dump(out, open(os.path.join(L.D, f'floors_{tag}.json'), 'w'), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}, indent=1))


if __name__ == '__main__':
    main()
