"""Replace expensive k6 keys of a pruned k7 set by cheap H9 keys (the k7 analogue of
full_product/extend.py).

With the potential pi of the pruned set (prune7: Bellman-Ford + revived dead states), a kept
k6 key is needed only for the critical transitions it alone covers.  Each of those
transitions has its own 9-direction window (H9 key, a2..a8 counted); when every one of them
is UNSAT the k6 key can go and those H9 keys come in (each costs about 2-100 k hints against
0.1-100 M for a k6 key).  Keys are tried by decreasing cost / number of transitions to cut,
within a time budget.  The new H9 keys go to data/oracle_k7.jsonl.gz; rerun prune7 after.

  nice -n 19 python replace7.py LAM TAG HOURS [MAXCUT] [--giants]   (--giants: most expensive first)
A replacement is taken only when its new H9 keys cost less (binned model) than the k6 key.
"""
import sys, os, json, time, gzip
sys.dont_write_bytecode = True
import numpy as np
import k7
import prune7 as PR7
from k7 import NC, NT

HERE = k7.HERE


def main():
    lam, tag, hours = float(sys.argv[1]), sys.argv[2], float(sys.argv[3])
    maxcut = int(sys.argv[4]) if len(sys.argv) > 4 and not sys.argv[4].startswith('-') else 400
    t0 = time.time()
    d = json.load(gzip.open(os.path.join(HERE, 'data', f'keys_{tag}.json.gz'), 'rt'))
    P, Q, B = k7.best_pq(lam); L = 2 ** B - 1
    S = k7.status()
    O = k7.Oracle()
    k6 = [(tuple(k[1]), tuple(k[2])) for k in d['keys'] if k[0] == 'k6']
    cst = {(tuple(k[1]), tuple(k[2])): c for k, c in zip(d['keys'], d['cost']) if k[0] == 'k6'}
    K = k7.K7(S, k6)
    for k in d['keys']:
        if k[0] != 'k6':
            K.add_new((k[0], tuple(k[1]), tuple(k[2])))
    conv, pi, pred, it = K.bf(P, Q, L)
    assert conv and pi.min() >= -L
    PR7.dead_potential(K, pi, P, Q, L)
    crit = PR7.critical(K, pi, P, Q)
    cv = PR7.Cover(K)
    cand = []
    for k in k6:
        if cst[k] <= 0:
            continue
        sl = cv.merge(cv.slabs6(k))
        u = [(i, f[crit[i, f] & (cv.cov[i, f] <= c)]) for i, f, c in sl]
        n = sum(len(f) for _, f in u)
        cand.append((cst[k] / max(n, 1), n, k))
    cand.sort(key=lambda x: -x[0] if '--giants' not in sys.argv else -cst[x[2]])
    ns = np.array([c[1] for c in cand]); cs = np.array([cst[c[2]] for c in cand])
    print(f'{len(cand)} costly k6 keys, {cs.sum() / 1e9:.2f} G hints; unique critical transitions: '
          f'median {int(np.median(ns))}, <= {maxcut}: {int((ns <= maxcut).sum())} keys / '
          f'{cs[ns <= maxcut].sum() / 1e9:.2f} G', flush=True)
    rep = gained = added = tested = 0
    log = []
    for ratio, n, k in cand:
        if time.time() - t0 > hours * 3600:
            break
        if n > maxcut or ratio < 2e5:
            continue
        spent = 0.0
        sl = cv.merge(cv.slabs6(k))
        ok, newk = True, []
        for i, f, c in sl:
            for x in f[crit[i, f] & (cv.cov[i, f] <= c)]:
                cnt = k7.digits(int(x), 7)
                hk = k7.h9_key(K.X[i], cnt)
                tested += hk not in O.st
                if O.get(hk) != 'UNSAT':
                    ok = False; break
                if hk not in K.newkeys and hk not in newk:
                    spent += PR7.new_cost(O.sec[hk])
                if spent >= cst[k]:          # the replacement would cost more than the key
                    ok = False; break
                newk.append(hk)
            if not ok:
                break
        if ok:
            for hk in newk:
                if hk not in K.newkeys:
                    K.newkeys.add(hk)
                    for i, c in K.hits_new(hk):
                        cv.cov[i, k7.cidx(c)] += 1
                    added += 1
            for i, f, c in sl:
                cv.cov[i, f] -= c
            rep += 1; gained += cst[k]
        log.append(dict(key=[list(k[0]), list(k[1])], cost=cst[k], cut=n, replaced=ok, new_cost=round(spent)))
        if '--giants' in sys.argv:
            print(json.dumps(log[-1]), flush=True)
        if len(log) % 50 == 0:
            print(f'{len(log)} tried, {rep} replaced, {gained / 1e9:.2f} G hints saved, {added} H9 added, '
                  f'{tested} decided, {time.time() - t0:.0f}s', flush=True)
            O.flush()
    O.flush()
    res = dict(giants='--giants' in sys.argv, tag=tag, tried=len(log), replaced=rep, saved_hints=gained, h9_added=added, decided=tested,
               seconds=round(time.time() - t0))
    print(json.dumps(res), flush=True)
    json.dump(dict(result=res, tried=log), open(os.path.join(HERE, 'data', f'replace_{tag}{"_giants" if "--giants" in sys.argv else ""}.json'), 'w'))


if __name__ == '__main__':
    main()
