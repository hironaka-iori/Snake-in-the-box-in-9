"""Stage D: the certificates a share-weighted k6 chain at lambda_t = P/Q needs (dual pruning with one
potential), and their cost.

1. Bellman-Ford from 0 for Q (120 A + S5lb) - P on the allowed transitions of the full product
   (every known plain exclusion, every share lb) gives pi with range R; the integer bound is
   comb.bound_m(P, Q, R, 1, 0, 0).
2. Share certificates.  An allowed transition with Q 120 A - P + pi(u) - pi(v) < 0 needs its trailing
   5-window to carry share >= T(e) = ceil(deficit / Q).  Per 5-window key the needed T is the max
   over its transitions (usually below the proved lb, so a cheaper certificate than the one found).
   Free when a Lean floor of origin/main covers it (shape 012032/012031/012304/012314, T <= 16; the
   share-17 count condition), else a new RefutedShare certificate.
3. Plain certificates.  An excluded transition with Q (120 A + S5lb) - P + pi(u) - pi(v) < 0 must stay
   excluded: one of its UNSAT suffix windows (2..6 counts) has to be a key.  Greedy weighted hitting
   set (free keys first: the 1,383 Lean-replayed ones), then reverse delete.  With pi fixed the step
   check then holds on every transition the chosen keys leave allowed.
4. Costs.  Plain: 23-k6-lean/full_product/prune.load_costs (measured, est_r4, 1.49e6 t^0.843 on the
   key's own solve time, class median); this milestone's own keys by the same fit on their seconds.
   Share: 1.0 M hints per solver-second of the threshold call that proved the needed level or more
   (share_samples.py: 0.7-1.0 M per second on 6 samples of this run), min 12 k.  Disk/olean: 2.9 B per hint (milestone 26).
usage: certplan.py P/Q
"""
import sys, os, json, time, itertools, glob, gzip
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
sys.path.insert(0, os.path.join(C.MS, '23-k6-lean', 'full_product'))
import prune as PR

NT, NC = C.NT, C.NC
CERT_SHAPES = {(0, 1, 2, 0, 3, 2), (0, 1, 2, 0, 3, 1), (0, 1, 2, 3, 0, 4), (0, 1, 2, 3, 1, 4)}


def own_seconds():
    sec = {}
    for f in sorted(glob.glob(os.path.join(HERE, 'data', 'oracle_plain*.jsonl'))):
        for l in open(f):
            r = json.loads(l)
            if r['result'] == 'UNSAT':
                k = PR.lumped_of(r['dirs'], r['alpha'])
                if k:
                    sec[k] = float(r['seconds'])
    return sec


def share_seconds():
    """Per lumped 5-key: list of (T, seconds) of UNSAT threshold calls (all share oracles)."""
    files = [os.path.join(C.MS, '11-local-ceiling', 's0_share_loop', 'share_oracle.jsonl'),
             os.path.join(C.MS, '11-local-ceiling', 'k6_loop', 'oracle_share.jsonl'),
             os.path.join(C.MS, '11-local-ceiling', 's0_k6_ceiling', 'oracle5_extra.jsonl')] + \
        sorted(glob.glob(os.path.join(HERE, 'data', 'oracle_share*.jsonl')))
    out = {}
    for f in files:
        for l in open(f):
            r = json.loads(l)
            if r.get('kind') == 'thr' and r['result'] == 'UNSAT' and len(r['alpha']) == 5:
                for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                    out.setdefault(C.fp.lkey(tuple(r['dirs']), t), []).append((r['T'], float(r.get('seconds') or 0)))
    return out


def main():
    lam = Fr(sys.argv[1]); P, Q = lam.numerator, lam.denominator
    t0 = time.time()
    G = C.build('all', with_share=True, with_w3=False)
    n = int(G['n'])
    U = G['U'].astype(np.int64); V = G['V'].astype(np.int64)
    A = G['A'].astype(np.int64); S5 = G['S5'].astype(np.int64)
    pi, it = C.bellman_ford(n, U, V, Q * (120 * A + S5) - P, 40000)
    assert pi is not None, 'lambda_t above the minimum cycle mean'
    pi = pi - pi.min(); R = int(pi.max())
    bound = int(C.bound_m(P, Q, R, 1, 0, 0))
    C.log(f'lambda_t {lam}: BF {it} rounds, range {R} ({R / Q / 120:.2f} alpha units), bound {bound}')
    # ---- share needs
    red0 = Q * 120 * A - P + pi[U] - pi[V]
    bad = np.nonzero(red0 < 0)[0]
    needT = -(-(-red0[bad]) // Q)
    Pr = C.fp.Product()
    req = {}
    for e, T in zip(bad, needT):
        ds, t, k5, k6 = C.step_windows(int(G['G'][e]), Pr)
        req[k5] = max(req.get(k5, 0), int(T))
    ssec = share_seconds()
    sh = dict(lean=0, solver=0, hints=0.0, rows=[])
    for k, T in req.items():
        c = k[0]
        free = (c in CERT_SHAPES and T <= 16) or (c == (0, 1, 2, 0, 3, 2) and T <= 17 and k[1] in
                                                  [x for x in [(4, a, 4, b, 3) for a in range(1, 5) for b in range(1, 6)]] +
                                                  [(3, b, 4, a, 4) for a in range(1, 5) for b in range(1, 6)])
        if free:
            sh['lean'] += 1; continue
        cands = [s for (TT, s) in ssec.get(k, []) if TT >= T]
        s = min(cands) if cands else None
        h = max(1.2e4, 1.0e6 * s) if s is not None else None
        sh['solver'] += 1; sh['hints'] += h or 0
        sh['rows'].append(dict(key=[list(k[0]), list(k[1])], T=T, seconds=s, hints=h))
    C.log(f"share: {len(req)} keys needed, {sh['lean']} covered by Lean floors, {sh['solver']} solver "
          f"thresholds, est. {sh['hints'] / 1e9:.3f} G hints")
    # ---- plain needs: excluded transitions violating pi
    S = C.fp.Status()
    for k in C.own_plain_unsat():
        S.st[k] = 'UNSAT'
    keys = sorted(k for k, v in S.st.items() if v == 'UNSAT')
    for k in keys:
        Pr.apply(k)
    SD = C.share_dense(False)
    z5 = np.zeros(6 ** 5, np.int64)
    x = np.arange(NT)
    crit = []
    for e, (i, d, j, ds) in enumerate(Pr.ext):
        exc = np.nonzero(Pr.CNT[e] > 0)[0]
        if not len(exc):
            continue
        u = i * NC + exc // 6; v = j * NC + exc % NC
        w = 120 * (exc % 6 + 1) + SD.get(C.canon(ds[2:8]), z5)[exc % 7776]
        r = Q * w - P + pi[u] - pi[v]
        crit.append(e * NT + exc[r < 0])
    crit = np.concatenate(crit)
    C.log(f'{len(crit)} critical excluded transitions; {len(keys)} UNSAT keys known')
    cost, how, cert = PR.load_costs(keys, True)
    k235 = set(C.load_keyfile(os.path.join(C.MS, '23-k6-lean', 'full_product', 'keys_235.json')))
    osec = own_seconds()
    fit = json.load(open(os.path.join(C.MS, '23-k6-lean', 'full_product', 'costs.json')))
    for i, k in enumerate(keys):
        if k in k235 or k in cert:
            cost[i] = 0; how[i] = 'reuse'
        elif how[i] == 'median' and k in osec:
            f = fit.get(str(len(k[1])), fit['6'])
            cost[i] = f['A'] * max(osec[k], 0.01) ** f['B'] + f['C']; how[i] = 'own_seconds'
    kid = {k: i for i, k in enumerate(keys)}
    # cover sets
    cover = []
    for g in crit:
        ks = [kid[k] for k in Pr.windows(int(g)) if k in kid]
        cover.append(ks)
    chosen = set()
    order = sorted(range(len(cover)), key=lambda q: min(cost[i] for i in cover[q]))
    for q in order:
        if any(i in chosen for i in cover[q]):
            continue
        chosen.add(min(cover[q], key=lambda i: cost[i]))
    # reverse delete (most expensive first)
    cnt = {}
    for ks in cover:
        c = sum(1 for i in ks if i in chosen)
        for i in ks:
            if i in chosen:
                cnt.setdefault(i, []).append(c)
    by = {}
    for q, ks in enumerate(cover):
        for i in ks:
            if i in chosen:
                by.setdefault(i, []).append(q)
    hits = np.array([sum(1 for i in ks if i in chosen) for ks in cover])
    for i in sorted(chosen, key=lambda i: -cost[i]):
        qs = by.get(i, [])
        if all(hits[q] >= 2 for q in qs):
            chosen.discard(i)
            for q in qs:
                hits[q] -= 1
    ch = sorted(chosen)
    basis = {}
    for i in ch:
        b = how[i]; basis.setdefault(b, [0, 0.0]); basis[b][0] += 1; basis[b][1] += cost[i]
    plain_hints = float(sum(cost[i] for i in ch))
    ncent = {}
    for i in ch:
        if how[i] != 'reuse':
            ncent[len(keys[i][1])] = ncent.get(len(keys[i][1]), 0) + 1
    C.log(f'plain: {len(ch)} keys ({sum(1 for i in ch if how[i] == "reuse")} reused), '
          f'est. {plain_hints / 1e9:.3f} G hints; by basis {basis}')
    tot = plain_hints + sh['hints']
    out = dict(lam=str(lam), P=P, Q=Q, R=R, R_alpha=R / Q / 120, bf_rounds=it, bound=bound,
               share=dict(needed=len(req), lean=sh['lean'], solver=sh['solver'], hints=sh['hints']),
               plain=dict(keys=len(ch), reused=sum(1 for i in ch if how[i] == 'reuse'), new_by_centres=ncent,
                          hints=plain_hints, basis={k: [v[0], round(v[1])] for k, v in basis.items()},
                          critical_transitions=int(len(crit))),
               total_hints=tot, kernel_hours_042=tot * 0.42e-3 / 3600, olean_GB=tot * 2.9 / 1e9,
               seconds=round(time.time() - t0))
    print(json.dumps(out), flush=True)
    out['share_rows'] = sorted(sh['rows'], key=lambda r: -(r['hints'] or 0))
    out['plain_keys'] = [[list(keys[i][0]), [list(C.LUMP[s]) for s in keys[i][1]], how[i], round(float(cost[i]))] for i in ch]
    json.dump(out, open(os.path.join(HERE, 'data', f'certplan_{P}_{Q}.json'), 'w'))


if __name__ == '__main__':
    main()
