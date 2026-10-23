"""Share-weighted plain refinement and pruning on the FULL k6 product.

Weight of a transition: w = 24 s + B * [hw6 window has shape 0123415], s the new lumped count.
Target: lambda' = P (integer, in 24-alpha units) with a potential of range <= LIM, i.e. no walk
of the full product has sum(w - P) < -LIM.  Exclusions: every known radius-4 plain UNSAT key
(fp.Status: k6_loop, k6_w3, k6_w3_loop, radius-4 caches, oracle_full.jsonl) plus this
directory's oracle_share_bonus.jsonl (k6loop record format).

usage:
  nice -n 19 python refine_share.py eval B [B ...]          MCM with all known keys
  nice -n 19 python refine_share.py loop P B LIM HOURS [MAXTEST] [TL]
  nice -n 19 python refine_share.py prune TAG P B LIM [--drop-budget S] [--base-free]
        cost-aware pruning (prune.py) from all known keys, the replayed 236/237 keys free
        (and with --base-free the keys of keys_235.json); writes keys_<TAG>.json, prune_<TAG>.json.
"""
import sys, os, json, time, argparse
sys.dont_write_bytecode = True
for v in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[v] = '1'
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
FPD = os.path.join(MS, '23-k6-lean', 'full_product')
sys.path.insert(0, FPD)
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
import fp as FP
import prune as PR
import k6loop as K6
from refine import key as rkey, canon, prune as live_prune, howard
from fractions import Fraction as Fr

PAT = (0, 1, 2, 3, 4, 1, 5)
NC, NT = FP.NC, FP.NT
ORACLE = os.path.join(HERE, 'oracle_share_bonus.jsonl')
ROUNDS = os.path.join(HERE, 'rounds_share.jsonl')
K235 = os.path.join(FPD, 'keys_235.json')


def status():
    S = FP.Status()
    if os.path.exists(ORACLE):
        for l in open(ORACLE):
            r = json.loads(l)
            k = rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha']))
            S.P.put(k, r['result'], 'share_bonus')
            lk = PR.lumped_of(r['dirs'], r['alpha'])
            if S.st.get(lk) in (None, 'TIMEOUT'):
                S.st[lk] = r['result']; S.src[lk] = 'share_bonus'
    K6.OPLAIN = ORACLE
    return S


def pat_flags(Pr):
    return np.array([canon(ds[1:]) == PAT for (_, _, _, ds) in Pr.ext])


def weights(Pr, patE, g, P, B):
    u, v, s = Pr.uvw(g)
    return u, v, s, 24 * s + B * patE[g // NT] - P


def bf_pred(Pr, patE, P, B, lim, maxit=600, extra=6):
    g = np.flatnonzero((Pr.CNT == 0).ravel())
    u, v, s, w = weights(Pr, patE, g, P, B)
    o = np.argsort(v, kind='stable')
    g, u, v, w = g[o], u[o].astype(np.int32), v[o].astype(np.int32), w[o].astype(np.int32)
    uv, starts = np.unique(v, return_index=True)
    pi = np.zeros(Pr.n, np.int32); pred = np.full(Pr.n, -1, np.int64)
    first_bad = None
    for it in range(maxit):
        cand = pi[u] + w
        mins = np.minimum.reduceat(cand, starts)
        upd = mins < pi[uv]
        if not upd.any():
            return True, pi, pred, it
        um = np.zeros(Pr.n, bool); um[uv[upd]] = True
        pi[uv[upd]] = mins[upd]
        m = um[v] & (cand == pi[v])
        pred[v[m]] = g[m]
        if first_bad is None and pi.min() < -lim:
            first_bad = it
        if first_bad is not None and it >= first_bad + extra:
            break
    return False, pi, pred, it


def mcm(Pr, patE, B):
    g = np.flatnonzero((Pr.CNT == 0).ravel())
    u, v, s, w = weights(Pr, patE, g, 0, B)
    u = u.astype(np.int64); v = v.astype(np.int64)
    keep = np.flatnonzero(live_prune(Pr.n, u, v))
    mu, cyc = howard(Pr.n, u[keep], v[keep], w[keep], iters=400)
    cyc = [keep[e] for e in cyc]
    lam = Fr(int(w[cyc].sum()), len(cyc))
    return lam, dict(B=B, mean=str(lam), alpha_units=round(float(lam) / 24, 4), length=len(cyc),
                     counts=[int(s[e]) for e in cyc], pattern_edges=int(patE[g[cyc] // NT].sum()),
                     shapes=[FP.GA.lst(Pr.shp[int(u[e]) // NC]) for e in cyc])


def round_(S, Pr, patE, P, B, lim, maxtest, tl):
    t0 = time.time()
    conv, pi, pred, it = bf_pred(Pr, patE, P, B, lim)
    rec = dict(time=time.strftime('%H:%M:%S'), converged=bool(conv), bf_it=int(it), pi_min=int(pi.min()),
               allowed=int((Pr.CNT == 0).sum()), keys=sum(1 for v in S.st.values() if v == 'UNSAT'))
    if conv and pi.min() >= -lim:
        rec['done'] = True; rec['range'] = int(-pi.min())
        return rec
    bad = np.flatnonzero(pi < -lim)
    if len(bad) == 0:
        bad = np.flatnonzero(pred >= 0)
    bad = bad[np.argsort(pi[bad], kind='stable')][:3000]
    freq = {}; chains = []; ncyc = 0
    for x in bad:
        ch, cyc = Pr.chain(pi, pred, int(x))
        ncyc += cyc; chains.append((ch, cyc))
        for g in ch:
            freq[g] = freq.get(g, 0) + 1
    rec.update(violators=int((pi < -lim).sum()), chains=len(chains), cycles=int(ncyc), chain_edges=len(freq))
    tested = unsat = 0; hard = set(); removed = set(); tsec = 0.0
    for g in sorted(freq, key=lambda g: -freq[g]):
        if tested >= maxtest:
            break
        ok = False
        for k in Pr.windows(g):
            st = S.st.get(k)
            if st == 'UNSAT':
                ok = True; break
            if st is None:
                r = S.test(k, tl if len(k[1]) == 6 else tl / 2); tested += 1; tsec += r['seconds']
                if r['result'] == 'UNSAT':
                    Pr.apply(k); unsat += 1; ok = True; break
        (removed if ok else hard).add(g)
    obs = [c for c in chains if all(g in hard for g in c[0])]
    rec.update(tested=tested, unsat=unsat, solve_s=round(tsec, 1), removed=len(removed), hard_edges=len(hard),
               obstructions=len(obs), round_s=round(time.time() - t0, 1), rss=round(FP.rss_mb()))
    if obs:
        ch, cyc = min(obs, key=lambda c: (not c[1], len(c[0])))
        gg = np.array(ch, np.int64)
        _, _, s, w = weights(Pr, patE, gg, P, B)
        rec['obstruction'] = dict(cycle=cyc, len=len(ch), counts=[int(x) for x in s], weight=int(w.sum()),
                                  pattern_edges=int(patE[gg // NT].sum()))
    if tested == 0:
        rec['stuck'] = True
    return rec


def main():
    mode = sys.argv[1]
    t0 = time.time()
    S = status(); Pr = FP.Product(); FP.load_all(S, Pr); patE = pat_flags(Pr)
    print(f'{sum(1 for v in S.st.values() if v == "UNSAT")} lumped UNSAT keys, {Pr.n} states, '
          f'{int((Pr.CNT == 0).sum())} allowed transitions [{time.time()-t0:.0f}s, rss {FP.rss_mb():.0f} MB]',
          flush=True)
    if mode == 'eval':
        for B in map(int, sys.argv[2:]):
            lam, info = mcm(Pr, patE, B)
            print(json.dumps(info), flush=True)
        return
    if mode == 'loop':
        P, B, lim = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        hours = float(sys.argv[5]); maxtest = int(sys.argv[6]) if len(sys.argv) > 6 else 300
        tl = float(sys.argv[7]) if len(sys.argv) > 7 else 30
        t_end = time.time() + hours * 3600
        rnd = 0
        while time.time() < t_end:
            rec = round_(S, Pr, patE, P, B, lim, maxtest, tl)
            rec.update(round=rnd, P=P, B=B, lim=lim); rnd += 1
            print(json.dumps({k: v for k, v in rec.items() if k != 'obstruction'}), flush=True)
            if 'obstruction' in rec:
                print('OBSTRUCTION', json.dumps(rec['obstruction']), flush=True)
            with open(ROUNDS, 'a') as f:
                f.write(json.dumps(rec) + '\n')
            if rec.get('done') or rec.get('stuck'):
                break
        return
    if mode == 'prune':
        ap = argparse.ArgumentParser()
        ap.add_argument('mode'); ap.add_argument('tag'); ap.add_argument('P', type=int)
        ap.add_argument('B', type=int); ap.add_argument('lim', type=int)
        ap.add_argument('--drop-budget', type=float, default=1800)
        ap.add_argument('--base-free', action='store_true', help='keys of keys_235.json cost 0')
        ap.add_argument('--from', dest='frm', help='start from this key set (generator format)')
        a = ap.parse_args()
        do_prune(S, Pr, patE, a)


def do_prune(S, Pr, patE, a):
    t0 = time.time()
    PR.LIM = a.lim
    keys = sorted(S.unsat(), key=lambda k: (len(k[0]), k))
    cost, how, cert = PR.load_costs(keys, True)
    base = {PR.lumped_of(d, al) for d, al in json.load(open(K235))['keys']}
    full_cost = cost.copy()
    if a.base_free:
        for i, k in enumerate(keys):
            if k in base:
                cost[i] = 0
    N = PR.Net(Pr)
    gs = N.g
    s = (gs % NT) % 6 + 1
    N.w = (24 * s + a.B * patE[gs // NT] - a.P).astype(np.int32)
    ek = [N.pos[Pr.edges_of(k)] for k in keys]
    kept = np.ones(len(keys), bool)
    if a.frm:
        want = {PR.lumped_of(d, al) for d, al in json.load(open(a.frm))['keys']}
        kept = np.array([k in want for k in keys])
    for i in np.flatnonzero(kept):
        np.add.at(N.cnt, ek[i], 1)
    ok, pi = N.bf()
    print(f'{len(keys)} keys; start feasible {ok} range {-pi.min()} [{time.time()-t0:.0f}s, rss {FP.rss_mb():.0f} MB]',
          flush=True)
    assert ok
    for sweep in range(20):
        exc = N.cnt > 0
        sl = N.w + pi[N.u] - pi[N.v]
        crit = np.flatnonzero(exc & (sl < 0))
        emap = np.full(len(N.cnt), -1, np.int64); emap[crit] = np.arange(len(crit))
        cand = np.flatnonzero(kept)
        elems = {}
        for i in cand:
            e = emap[ek[i]]; elems[i] = e[e >= 0]
        keep = PR.greedy(elems, cost + 1.0, cand, len(crit))     # +1: fewer keys among free ones
        newk = np.zeros(len(keys), bool); newk[keep] = True
        newk &= kept
        for i in np.flatnonzero(kept & ~newk):
            np.subtract.at(N.cnt, ek[i], 1)
        changed = (newk != kept).any(); kept = newk
        ok, _ = N.bf(pi); assert ok
        ok, pi = N.bf()
        print(f' sweep {sweep}: critical {len(crit)}, kept {kept.sum()}, extra cost {cost[kept].sum()/1e6:.1f} M, '
              f'range {-pi.min()} [{time.time()-t0:.0f}s]', flush=True)
        if not changed:
            break
    t1 = time.time(); tried = dropped = 0
    for i in sorted(np.flatnonzero(kept), key=lambda i: -cost[i]):
        if time.time() - t1 > a.drop_budget or cost[i] <= 0:
            break
        tried += 1
        np.subtract.at(N.cnt, ek[i], 1)
        ok, pi2 = N.bf(pi)
        if ok:
            kept[i] = False; pi = pi2; dropped += 1
        else:
            np.add.at(N.cnt, ek[i], 1)
    ok, pi = N.bf(); assert ok
    ks = [keys[i] for i in np.flatnonzero(kept)]
    extra = [keys[i] for i in np.flatnonzero(kept) if keys[i] not in base]
    extra_new = [k for k in extra if k not in cert]
    new_all = [k for k in ks if k not in cert]
    hint = {keys[i]: full_cost[i] for i in np.flatnonzero(kept)}
    byc = {}
    for k in extra_new:
        byc[len(k[1])] = byc.get(len(k[1]), 0) + 1
    out = dict(tag=a.tag, P=a.P, B=a.B, lim=a.lim, kept=len(ks), from_keys_235=len(ks) - len(extra),
               extra=len(extra), extra_already_certified=len(extra) - len(extra_new),
               extra_new=len(extra_new), extra_new_by_centres=byc,
               extra_new_hints=float(sum(hint[k] for k in extra_new)),
               extra_new_max_hints=float(max([hint[k] for k in extra_new], default=0)),
               new_certificates=len(new_all), new_certificate_hints=float(sum(hint[k] for k in new_all)),
               potential_range=int(-pi.min()), base_free=a.base_free, start=a.frm and os.path.basename(a.frm), exact_tried=tried, exact_dropped=dropped,
               seconds=round(time.time() - t0))
    print(json.dumps(out), flush=True)
    json.dump(out, open(os.path.join(HERE, f'prune_{a.tag}.json'), 'w'), indent=1)
    json.dump(dict(keys=[[list(d), [list(FP.LUMP[x]) for x in t]] for d, t in ks]),
              open(os.path.join(HERE, f'keys_{a.tag}.json'), 'w'))


if __name__ == '__main__':
    main()
