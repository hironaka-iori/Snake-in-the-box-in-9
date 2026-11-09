"""The cost-reduction steps of milestone 31 on the share-weighted k6 product (driver).

  recost                 re-cost milestone 28's 520 plan (certplan_520_1) with measured data and the
                         calibrated models; check it on the full product (data/recost_520.json)
  prune LAM TAG          cost-aware dual reverse-delete on the full pool (all known plain keys, all
                         proved share levels), passes until stable
  giants TAG0 TAG MIN S  replace kept keys above MIN hints by longer windows of the critical
                         transitions only they cover (one-step extensions first, then longer;
                         new windows decided here, data/oracle_plain233.jsonl), or by share levels
  exact TAG0 TAG [MIN]   exact drops of plain keys (>= MIN hints) and exact share lowering, warm BF
  share TAG0 TAG S       re-solve the paid share thresholds at the level used (time limit S), so that
                         they are costed on their own solve time at that level
Every set is saved as data/set_TAG.json.gz with data/sum_TAG.json; LAM is P/Q/B or a float.
"""
import sys, os, json, time, gzip
import numpy as np
import lib233 as L
import eng233 as E
import wincert_share as ws

OPL = os.path.join(L.D, 'oracle_plain233.jsonl')
OSH = os.path.join(L.D, 'oracle_share233.jsonl')


def pq_of(s):
    if '/' in s:
        P, Q, B = map(int, s.split('/'))
        return P, Q, B
    P, Q, B, _ = L.best_pq(float(s))
    return P, Q, B


def own_oracle():
    st, sec = {}, {}
    if os.path.exists(OPL):
        for l in open(OPL):
            r = json.loads(l)
            k = L.PR.lumped_of(r['dirs'], r['alpha'])
            st[k] = r['result']; sec[k] = r['seconds']
    return st, sec


def pool_all():
    ks = set(L.plain_pool())
    st, _ = own_oracle()
    ks |= {k for k, v in st.items() if v == 'UNSAT'}
    return sorted(ks)


def world(pq, tag0=None):
    P, Q, B = pq
    W = E.World(P, Q, B, pool=pool_all())
    _, sec = own_oracle()
    PC = L.PlainCosts()
    for j, k in enumerate(W.keys):                  # this milestone's decisions: cost on own solve time
        if W.kbasis[j].startswith('median') and k in sec:
            t = sec[k] * PC.scale
            h, c, b = PC.C4.cls(f'k6_{len(k[1])}_{L.P4.sbin(t)}', (1.49e6 * max(t, 0.01) ** 0.843, 2000.0, 'fit'))
            W.khints[j] = h; W.kcore[j] = c; W.kbasis[j] = 'own233_' + b
            W.kcost[j] = h + E.OVH_CERT
    if tag0:
        miss = W.load(tag0)
        L.log(f'loaded {tag0} ({miss} keys missing from the pool)')
    return W


def decide_plain(lk, tl=20.0):
    while L.disk_mb() < 300:
        L.log('disk below 300 MB: waiting'); time.sleep(60)
    k = L.C.rkey_of(lk)
    enc = ws.from_key(k)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='plain', k=len(k[1]), result=st,
             cuts=cuts, seconds=round(sec, 3), nv=enc.nv, ncl=len(enc.clauses))
    with open(OPL, 'a') as f:
        f.write(json.dumps(r) + '\n')
    return st, sec


def decide_share(lk, T, tl=60.0):
    while L.disk_mb() < 300:
        L.log('disk below 300 MB: waiting'); time.sleep(60)
    k = L.C.rkey_of(lk)
    enc = ws.from_key(k, M=12, cap=T - 1)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='thr', T=T, result=st,
             witness=ws.share_exact(enc, sel, 12) if sel else None, cuts=cuts, seconds=round(sec, 2),
             nv=enc.nv, ncl=len(enc.clauses))
    with open(OSH, 'a') as f:
        f.write(json.dumps(r) + '\n')
    return st, sec


# ------------------------------------------------------------------ steps
def recost():
    """Step 1: the 520 plan of milestone 28 on the measured / calibrated cost basis."""
    plan = json.load(gzip.open(os.path.join(L.M28, 'data', 'certplan_520_1.json.gz'), 'rt'))
    W = world((520, 1, 10))
    ch = W.kfree.copy(); miss = 0
    for d, al, how, c in plan['plain_keys']:
        k = L.PR.lumped_of(d, al); j = W.kid.get(k)
        if j is None:
            miss += 1
        else:
            ch[j] = True
    W.set_chosen(ch)
    W.lvl = W.sF.copy()
    for r in plan['share_rows']:
        i = W.k5id[(tuple(r['key'][0]), tuple(r['key'][1]))]
        W.lvl[i] = max(W.lvl[i], r['T'])
    ok, it, rng = W.check()
    s = W.save('recost520', dict(check=dict(converged=bool(ok), rounds=it, range=rng), missing=miss,
                                 old_estimate=dict(plain=plan['plain']['hints'], share=plan['share']['hints'])))
    L.log(json.dumps(s))
    return s


def prune(pq, tag, passes=6):
    W = world(pq)
    ok, it, rng = W.check()
    assert ok, ('full pool does not meet the target', rng)
    hist = []
    for p in range(passes):
        dk, ds, nc = W.dual()
        ok, it, rng = W.check()
        assert ok
        rec = dict(passes=p, dropped=dk, lowered=ds, critical=nc, range=rng, bf_rounds=it,
                   objective=W.summary()['objective'])
        L.log(json.dumps(rec)); hist.append(rec)
        if dk == 0 and ds == 0:
            break
    return W.save(tag, dict(step='prune', passes=hist))


def critical_state(W):
    Q, P = W.Q, W.P
    red0 = Q * 120 * W.s - P + W.pi[W.u] - W.pi[W.v]
    crit = red0 < 0
    need = np.where(crit, (-red0 + Q - 1) // Q, 0)
    shcov = crit & (W.lvl[W.k5] >= need)
    return crit, need, shcov


def key_hints(k, sec, PC):
    t = sec.get(k, 0.05) * PC.scale
    h, _, _ = PC.C4.cls(f'k6_{len(k[1])}_{L.P4.sbin(t)}', (1.49e6 * max(t, 0.01) ** 0.843, 2000.0, 'fit'))
    return h


def giants(tag0, tag, mincost, budget, tls=(20.0, 90.0)):
    """For each kept key above mincost (most expensive first): the critical transitions only it
    covers (U) get their longer suffix windows decided (one more count first, then longer; a
    TIMEOUT is retried once with the longer limit); the cheapest cover of U by UNSAT windows and
    proved share levels is added; then the key is dropped if a warm Bellman-Ford keeps the range
    (so transitions of U left uncovered may still be absorbed by the potential).  If the drop
    fails, the added keys are removed again."""
    pq = tuple(json.load(open(os.path.join(L.D, f'sum_{tag0}.json')))[x] for x in ('P', 'Q', 'B'))
    W = world(pq, tag0)
    ok, it, rng = W.check(); assert ok
    st_own, sec_own = own_oracle()
    S = {k: 'UNSAT' for k in W.keys}
    Sfp = L.fp.Status()
    for k, v in Sfp.st.items():
        S.setdefault(k, v)
    for k, v in st_own.items():
        if S.get(k) != 'UNSAT':
            S[k] = v
    PC = L.PlainCosts()
    t0 = time.time(); log = []
    big = [int(j) for j in np.argsort(-W.kcost) if W.chosen[j] and not W.kfree[j] and W.khints[j] >= mincost]
    L.log(f'{len(big)} kept keys above {mincost:.0f} hints')
    for j in big:
        if time.time() - t0 > budget:
            break
        crit, need, shcov = critical_state(W)
        gs = W.hits(j)
        U = gs[crit[gs] & (W.cnt[gs] == 1) & ~shcov[gs]]
        wj = len(W.keys[j][1])
        cand = {}
        rem = set(range(len(U)))
        dec = dict(tested=0, unsat=0, timeout=0)
        for tl in tls:
            for w in range(wj + 1, 7):
                if not rem:
                    break
                groups = {}
                for q in rem:
                    k = W.Pr.windows(int(U[q]))[w - 2]
                    groups.setdefault(k, []).append(q)
                for k, qs in groups.items():
                    if time.time() - t0 > budget:
                        break
                    s = S.get(k)
                    if s is None or (s == 'TIMEOUT' and w == 6 and sec_own.get(k, tl) < tl - 1):
                        s, sec = decide_plain(k, tl); S[k] = s; sec_own[k] = sec
                        dec['tested'] += 1; dec['unsat'] += s == 'UNSAT'; dec['timeout'] += s == 'TIMEOUT'
                    if s == 'UNSAT':
                        cand[k] = set(qs)
                        rem -= set(qs)
        sopt = {}
        for q in range(len(U)):
            g = int(U[q]); i = int(W.k5[g])
            if need[g] <= W.slb[i]:
                sopt.setdefault(i, []).append(q)
        opts = []
        for k, qs in cand.items():
            jj = W.kid.get(k)
            c = (0.0 if W.chosen[jj] else W.kcost[jj]) if jj is not None else key_hints(k, sec_own, PC) + E.OVH_CERT
            opts.append(('k', k, c, qs))
        for i, qs in sopt.items():
            nl = max(int(need[int(U[q])]) for q in qs)
            c = max(0.0, W.share_obj(i, max(nl, W.lvl[i])) - W.share_obj(i, W.lvl[i]))
            opts.append(('s', i, c, set(qs)))
        left = set(range(len(U))); pick = []; tot = 0.0
        while left and opts:
            best = min(opts, key=lambda o: (o[2] + 1e-9) / len(o[3] & left) if o[3] & left else float('inf'))
            if not (best[3] & left):
                break
            pick.append(best); tot += best[2]; left -= best[3]
        rec = dict(key=[list(W.keys[j][0]), list(W.keys[j][1])], cost=round(W.khints[j]), U=len(U), decided=dec,
                   uncovered=len(left), replacement_cost=round(tot), n_new=sum(1 for p in pick if p[0] == 'k'),
                   n_share=sum(1 for p in pick if p[0] == 's'), replaced=False)
        if tot < W.kcost[j]:
            newk = [p[1] for p in pick if p[0] == 'k' and p[1] not in W.kid]
            if newk:
                add_keys(W, newk, sec_own, PC)
            added = []; oldlvl = {}
            for p in pick:
                if p[0] == 'k':
                    jj = W.kid[p[1]]
                    if not W.chosen[jj]:
                        W.chosen[jj] = True; W.cnt[W.hits(jj)] += 1; added.append(jj)
                else:
                    i = p[1]; nl = max(int(need[int(U[q])]) for q in p[3])
                    oldlvl[i] = W.lvl[i]; W.lvl[i] = max(W.lvl[i], nl)
            a_, d_, _ = W.exact_plain([j])
            if d_:
                rec['replaced'] = True
            else:
                for jj in added:
                    W.chosen[jj] = False; W.cnt[W.hits(jj)] -= 1
                for i, v in oldlvl.items():
                    W.lvl[i] = v
        rec['seconds'] = round(time.time() - t0)
        L.log(json.dumps(rec)); log.append(rec)
    ok, it, rng = W.check(); assert ok
    json.dump(log, open(os.path.join(L.D, f'giants_{tag}.json'), 'w'))
    return W.save(tag, dict(step='giants', replaced=sum(r['replaced'] for r in log), tried=len(log)))


def add_keys(W, newk, sec, PC):
    """Append new UNSAT keys to the pool (not chosen)."""
    segs = [W.Pr.edges_of(k).astype(np.int32) for k in newk]
    W.kg = np.concatenate([W.kg] + segs)
    W.kptr = np.concatenate([W.kptr, W.kptr[-1] + np.cumsum([len(x) for x in segs])])
    hs, cs, bs = [], [], []
    for k in newk:
        hs.append(key_hints(k, sec, PC)); cs.append(2000.0); bs.append('own233_model')
    for k in newk:
        W.kid[k] = len(W.keys); W.keys.append(k)
    W.nK = len(W.keys)
    W.khints = np.concatenate([W.khints, hs]); W.kcore = np.concatenate([W.kcore, cs]); W.kbasis += bs
    W.kfree = np.concatenate([W.kfree, np.zeros(len(newk), bool)])
    W.kcost = np.concatenate([W.kcost, np.array(hs) + E.OVH_CERT])
    W.chosen = np.concatenate([W.chosen, np.zeros(len(newk), bool)])


def exact(tag0, tag, mincost=0.0, budget=None, maxcost=None):
    pq = tuple(json.load(open(os.path.join(L.D, f'sum_{tag0}.json')))[x] for x in ('P', 'Q', 'B'))
    W = world(pq, tag0)
    ok, it, rng = W.check(); assert ok
    o0 = W.summary()['objective']
    # interleave plain keys and share keys by decreasing cost
    items = [(W.kcost[j], 0, int(j)) for j in np.flatnonzero(W.chosen & ~W.kfree)
             if W.khints[j] >= mincost and (maxcost is None or W.khints[j] < maxcost)]
    items += [(W.share_obj(i, W.lvl[i]), 1, int(i)) for i in np.flatnonzero(W.lvl > W.sF)]
    items.sort(key=lambda t: -t[0])
    t0 = time.time(); st = dict(plain_tried=0, plain_dropped=0, share_tried=0, share_lowered=0)
    for n, (c, kind, j) in enumerate(items):
        if budget and time.time() - t0 > budget:
            break
        if kind == 0:
            a, b, _ = W.exact_plain([j]); st['plain_tried'] += a; st['plain_dropped'] += b
        else:
            a, b, _ = W.exact_share([j]); st['share_tried'] += a; st['share_lowered'] += b
        if n % 1000 == 999:
            L.log(f'  exact {n + 1}/{len(items)}: {st}, objective {W.summary()["objective"] / 1e9:.3f} G')
    ok, it, rng = W.check(); assert ok
    st['seconds'] = round(time.time() - t0)
    st['objective_before'] = o0
    return W.save(tag, dict(step='exact', exact=st))


def share_resolve(tag0, tag, tl=60.0, budget=3600, minh=0.0):
    """Re-solve each paid share threshold at the level the set uses, cheapest-first by nothing:
    most expensive first, so that it is costed on its own solve time at that level."""
    pq = tuple(json.load(open(os.path.join(L.D, f'sum_{tag0}.json')))[x] for x in ('P', 'Q', 'B'))
    W = world(pq, tag0)
    done = set()
    if os.path.exists(OSH):
        for l in open(OSH):
            r = json.loads(l)
            done.add((L.lk_of(r['dirs'], [L.fp.lumped_choices(tuple(a))[0] for a in r['alpha']]), r['T']))
    rows = []
    for i in np.flatnonzero(W.lvl > W.sF):
        h, b = W.share_cost(i, W.lvl[i])
        if h >= minh:
            rows.append((h, int(i)))
    rows.sort(reverse=True)
    t0 = time.time(); res = {}
    for h, i in rows:
        if time.time() - t0 > budget:
            break
        k = W.k5keys[i]; T = int(W.lvl[i])
        if (k, T) in done:
            continue
        s, sec = decide_share(k, T, tl)
        res[s] = res.get(s, 0) + 1
        L.log(f'share {k} T={T} (lb {W.slb[i]}): {s} {sec:.1f}s, was {h / 1e6:.1f} M')
    W2 = world(pq, tag0)
    ok, it, rng = W2.check(); assert ok
    return W2.save(tag, dict(step='share_resolve', results=res))


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'recost':
        recost()
    elif cmd == 'prune':
        prune(pq_of(sys.argv[2]), sys.argv[3])
    elif cmd == 'giants':
        giants(sys.argv[2], sys.argv[3], float(sys.argv[4]), float(sys.argv[5]))
    elif cmd == 'exact':
        exact(sys.argv[2], sys.argv[3], float(sys.argv[4]) if len(sys.argv) > 4 else 0.0,
              float(sys.argv[5]) if len(sys.argv) > 5 else None)
    elif cmd == 'share':
        share_resolve(sys.argv[2], sys.argv[3], float(sys.argv[4]) if len(sys.argv) > 4 else 60,
                      float(sys.argv[5]) if len(sys.argv) > 5 else 3600)
