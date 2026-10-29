"""Replace expensive k6 keys of a pruned set by H9 keys (replace7 with the measured cost model of
prune234, the overhead per key included, and no cap on the number of cut transitions).

  nice -n 10 python replace234.py LAM TAG HOURS [--maxcut N] [--min COST] [--ovh 1]
Writes data/replace234_TAG.json; new H9 decisions go to data/oracle234.jsonl.gz.
"""
import sys, os, json, time, gzip, argparse
sys.dont_write_bytecode = True
import numpy as np
import k7
import prune7 as PR7
import prune234 as P4


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('lam', type=float); ap.add_argument('tag'); ap.add_argument('hours', type=float)
    ap.add_argument('--maxcut', type=int, default=20000); ap.add_argument('--min', type=float, default=2e5)
    ap.add_argument('--ovh', type=float, default=1.0); ap.add_argument('--pq', default=None)
    a = ap.parse_args()
    t0 = time.time()
    d = json.load(gzip.open(os.path.join(P4.D, f'keys_{a.tag}.json.gz'), 'rt'))
    s = d['summary']; P, Q, B = s['P'], s['Q'], s['B']; L = 2 ** B - 1
    S = k7.status(); O = P4.Oracle(); C = P4.Costs(a.ovh)
    k6 = [(tuple(k[1]), tuple(k[2])) for k in d['keys'] if k[0] == 'k6']
    cst = {k: C.eff(*C.k6(k)) for k in k6}
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
        if cst[k] < a.min:
            continue
        sl = cv.merge(cv.slabs6(k))
        n = sum(int((crit[i, f] & (cv.cov[i, f] <= c)).sum()) for i, f, c in sl)
        cand.append((cst[k] / max(n, 1), n, k))
    cand.sort(key=lambda x: -x[0])
    print(f'{len(cand)} k6 keys above {a.min:.0f}: {sum(cst[c[2]] for c in cand) / 1e9:.2f} G; '
          f'unique critical: median {int(np.median([c[1] for c in cand]))}', flush=True)
    rep = gained = added = tested = 0
    log = []
    for ratio, n, k in cand:
        if time.time() - t0 > a.hours * 3600:
            break
        if n > a.maxcut:
            continue
        spent = 0.0
        sl = cv.merge(cv.slabs6(k))
        ok, newk = True, []
        for i, f, c in sl:
            for x in f[crit[i, f] & (cv.cov[i, f] <= c)]:
                hk = k7.h9_key(K.X[i], k7.digits(int(x), 7))
                tested += hk not in O.st
                if O.get(hk) != 'UNSAT':
                    ok = False; break
                if hk not in K.newkeys and hk not in newk:
                    spent += C.eff(*C.new(hk, O.sec[hk]))
                    newk.append(hk)
                if spent >= cst[k]:
                    ok = False; break
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
            rep += 1; gained += cst[k] - spent
        log.append(dict(key=[list(k[0]), list(k[1])], cost=round(cst[k]), cut=n, replaced=ok, new_cost=round(spent)))
        if len(log) % 25 == 0 or n > 1000:
            print(f'{len(log)} tried, {rep} replaced, {gained / 1e9:.3f} G net saved, {added} H9 added, '
                  f'{tested} decided, {time.time() - t0:.0f}s | last {log[-1]}', flush=True)
            O.flush()
    O.flush()
    res = dict(tag=a.tag, tried=len(log), replaced=rep, net_saved=round(gained), h9_added=added, decided=tested,
               seconds=round(time.time() - t0))
    print(json.dumps(res), flush=True)
    json.dump(dict(result=res, tried=log), open(os.path.join(P4.D, f'replace234_{a.tag}.json'), 'w'))
    # the replaced set: k6 keys not replaced + every F8/H9 key (old and added)
    gone = {(tuple(x['key'][0]), tuple(x['key'][1])) for x in log if x['replaced']}
    d['keys'] = ([['k6', list(k[0]), list(k[1])] for k in k6 if k not in gone]
                 + [[k[0], list(k[1]), list(k[2])] for k in sorted(K.newkeys)])
    d['summary'] = dict(s, tag=a.tag + 'r')
    for x in ('hints', 'core', 'basis'):
        d.pop(x, None)
    json.dump(d, gzip.open(os.path.join(P4.D, f'keys_{a.tag}r.json.gz'), 'wt'))


if __name__ == '__main__':
    main()
