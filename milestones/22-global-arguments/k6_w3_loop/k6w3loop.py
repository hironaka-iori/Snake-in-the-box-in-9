"""k6 refinement loop with six-centre w_3 weights (solver side only).

Graph: the radius-4 L7 k6 K5 automaton of ../../11-local-ceiling/k6_loop (61,999 nodes, 1.0 M edges),
pruned by every plain alpha exclusion known (radius-4 caches of milestones 10/11, ../k6_w3 and this run).
Each edge e carries a 6-window key K6(e) (6 centres).  Its weight is a certified lower bound on the
6-window charge  sum_{6 centres} c(x),  c(x) = sum_Q floor(12/|Q cap S|):

    W6(K) = max( lb6(K),                      proved 6-window threshold (w3_survey encoding, sym. breaking)
                 lb5(left5(K))  + s(alpha_6),  proved 5-window threshold (or DP floor) + single-centre min
                 s(alpha_1) + lb5(right5(K)) )

Every internal vertex lies in exactly 6 consecutive 6-windows, so with lambda6 = min cycle mean of W6,
mu = lambda6 / 6 is a lower bound on the per-vertex mean of c and m <= 7 + 63148/mu (boundary terms for
k = 6 not re-derived; they move m by < 0.1).  For comparison the loop also reports lambda5/5 with the
T5 weights of ../k6_w3 on the same graph.

Round: Howard's minimum cycle of W6; target t = ceil(lambda6) + DELTA; for every distinct 6-key on the
cycle with W6 < t:  plain test of the 6-window if its status is unknown (UNSAT removes the edge);
then the cheaper of the two 5-sub-window thresholds that would lift W6 to t (incremental ascending
ladder need, need+10, ... while each step is cheap); if neither can (witness below need, or timeout),
the 6-window threshold ladder t, t+10, ...  Every solver call is one line of data/w3_loop_oracle.jsonl
(w3survey record format), every round one line of data/rounds.jsonl.  Every SAMPLE-th UNSAT threshold
is re-solved cold with CaDiCaL --lrat and its trimmed hint count logged (data/proof_samples.jsonl).

Ceiling: the minimum cycle mean of ub6 (exact charge of a SAT witness of the 6-window) over live edges
whose 6-window has a witness: no set of 6-window w_3 thresholds on this automaton proves more there.

usage: k6w3loop.py HOURS [DELTA] [SAMPLE]
"""
import sys, os, json, time, math
ME = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(ME, '..', 'k6_w3'))
from fractions import Fraction as Fr
from k6w3lib import *            # G loaders, survey, w3enc, k6loop, howard, exact_check, live, masks
import refine_w3 as R

DATA = os.path.join(ME, 'data')
OW = os.path.join(DATA, 'w3_loop_oracle.jsonl')
OPL = os.path.join(DATA, 'plain_loop.jsonl')
ROUNDS = os.path.join(DATA, 'rounds.jsonl')
PROOFS = os.path.join(DATA, 'proof_samples.jsonl')
SCR = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/k6w3loop'
K6W3 = os.path.join(ME, '..', 'k6_w3', 'data')
W3S = os.path.join(ME, '..', 'w3_survey', 'data')
CHEAP = 8.0            # keep raising a key's threshold while the last UNSAT took < CHEAP s
TL5, TL6 = 60, 150
BULK = int(os.environ.get("BULK", 1500))
from collections import Counter


def setup():
    G = build(); P = Plain()
    for f in (os.path.join(K6W3, 'plain_k6w3.jsonl'), OPL):
        if os.path.exists(f):
            for l in open(f):
                r = json.loads(l)
                P.put(k6loop.rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])), r['result'], 'here')
    k6loop.OPLAIN = OPL
    O = survey.Oracle(OW)
    for f in (os.path.join(K6W3, 'w3_k6_oracle.jsonl'), os.path.join(W3S, 'w3_alpha_oracle.jsonl')):
        for l in open(f):
            O.apply(json.loads(l))
    sub = R.Sub()
    for k, s in O.st.items():
        if s['excl']:
            P.put(k, 'UNSAT', 'w3excl')
    return G, P, O, sub


class Tables:
    """Per 6-key: ids of its two 5-sub-windows (extended 5-key list) and single-centre floors."""
    def __init__(self, G, sub):
        self.k5 = list(G['keys5']); self.id5 = {k: i for i, k in enumerate(self.k5)}
        n = len(G['keys6'])
        self.L = np.empty(n, np.int64); self.R = np.empty(n, np.int64)
        self.sF = np.empty(n, np.int64); self.sL = np.empty(n, np.int64)
        sc = {}
        for j, (ds, al) in enumerate(G['keys6']):
            for arr, kk in ((self.L, survey.key(ds[0:6], al[0:5])), (self.R, survey.key(ds[1:7], al[1:6]))):
                if kk not in self.id5:
                    self.id5[kk] = len(self.k5); self.k5.append(kk)
                arr[j] = self.id5[kk]
            for arr, a in ((self.sF, al[0]), (self.sL, al[5])):
                if a not in sc:
                    sc[a] = sub.single_lb(a)
                arr[j] = sc[a]
        self.floor5 = np.array([sub.floor5(k) for k in self.k5], np.int64)

    def weights(self, G, O):
        lb5 = self.floor5.copy()
        for i, k in enumerate(self.k5):
            s = O.st.get(k)
            if s and s['lb'] > lb5[i]:
                lb5[i] = s['lb']
        lb6 = np.zeros(len(G['keys6']), np.int64); ub6 = np.full(len(G['keys6']), INF, np.int64)
        for j, k in enumerate(G['keys6']):
            s = O.st.get(k)
            if s:
                lb6[j] = s['lb']
                if s['ub'] is not None:
                    ub6[j] = s['ub']
        W6 = np.maximum(lb6, np.maximum(lb5[self.L] + self.sL, self.sF + lb5[self.R]))
        return W6, lb5, ub6


# ------------------------------------------------------------------ solver calls
NUNSAT = [0]


def ladder(k, Ts, tl, O, sample=0, tag='loop'):
    """Ascending thresholds on one incremental solver: stop at SAT, TIMEOUT or the first slow UNSAT.
    Returns the list of (T, result, seconds)."""
    ds, al = k
    w = w3enc.window_from_dirs(list(ds)); nc = len(w) - 2
    survey.wait_mem()
    t0 = time.time()
    enc = survey.IncW3(w, survey.alpha_arg(al), 4, max(Ts) + 1)
    root = enc.root_outputs
    build_s = time.time() - t0
    ncl0 = len(enc.clauses)
    base = dict(dirs=list(ds), alpha=[list(a) for a in al], kind=tag)
    out = []
    with survey.Cadical153(bootstrap_with=enc.clauses) as sv:
        for T in Ts:
            s = O.get(k)
            if T <= s['lb'] or (s['ub'] is not None and T > s['ub']):
                continue
            idx = T - 168 * nc
            if idx < 1:
                continue
            st, sel, cuts, sec = survey.solve_assume(sv, enc, [-root[idx]], tl)
            wv = w3enc.window_charge(w, sel) if sel else None
            O.log(dict(base, T=T, result=st, witness=wv, seconds=round(sec, 1), cuts=cuts, nv=enc.nv,
                       sym=enc.SYM, ncl=len(enc.clauses) + 1, build=round(build_s, 1), rss=round(rss_mb())))
            out.append((T, st, round(sec, 1), wv))
            if st != 'UNSAT':
                break
            NUNSAT[0] += 1
            if sample and NUNSAT[0] % sample == 0:
                measure(k, T, enc.clauses[ncl0:], len(w) - 2)
            if sec > CHEAP:
                break
    return out


def measure(k, T, cuts, nc):
    """Cold CaDiCaL --lrat of the static threshold CNF (cap T-1, the incremental run's cycle cuts),
    trimmed; proof files deleted after counting."""
    ds, al = k
    w = w3enc.window_from_dirs(list(ds))
    enc = w3enc.W3Encoding(w, survey.alpha_arg(al), 4, T - 1)
    for c in cuts:
        enc.clauses.append(list(c))
    w3enc.FSIZE_KB = 45 * 1024
    t = time.time()
    r = w3enc.measure_proof(enc, SCR, timeout=600)
    r.update(dirs=list(ds), alpha=[list(a) for a in al], centres=nc, T=T, wall=round(time.time() - t, 1))
    with open(PROOFS, 'a') as f:
        f.write(json.dumps(r) + '\n')
    print('   proof sample', keystr(k), T, {x: r.get(x) for x in ('lrat_hints', 'lrat_seconds', 'failed', 'timeout')}, flush=True)


RANGE = os.environ.get('RANGE', '1') == '1'


def range_test(P, mem):
    """One plain test of the 6-window whose first-centre alpha is the hull of the members' values
    (the other five alpha and the directions are shared).  UNSAT excludes every member: logged as
    one 'plainrange' record plus one derived 'plain' UNSAT record per member (src 'range')."""
    ds = mem[0][0]; rest = mem[0][1][1:]
    lo = min(k[1][0][0] for k in mem); hi = max(k[1][0][1] for k in mem)
    rk = (ds, ((lo, hi),) + rest)
    k6loop.wait_res()
    enc = k6loop.ws.from_key(rk)
    st, sel, cuts, sec = k6loop.ws.solve(enc, 20)
    with open(OPL, 'a') as f:
        f.write(json.dumps(dict(dirs=list(ds), alpha=[list(a) for a in rk[1]], kind='plainrange', k=6, result=st,
                                cuts=cuts, seconds=round(sec, 2), members=len(mem))) + '\n')
        if st == 'UNSAT':
            for k in mem:
                f.write(json.dumps(dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='plain', k=6,
                                        result='UNSAT', src='range', via=[list(a) for a in rk[1]])) + '\n')
                P.put(k, 'UNSAT', 'range')
    return st


# ------------------------------------------------------------------ loop
def evaluate(G, P, O, Tb, extra=False):
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    W6, lb5, ub6 = Tb.weights(G, O)
    w = W6[G['K6'][idx]]
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    res = dict(lam6=lam, mu6=float(lam) / 6, cyc=[int(idx[e]) for e in cyc], idx=idx, W6=W6, lb5=lb5, ub6=ub6)
    if extra:
        w5 = lb5[G['K5'][idx]]
        _, c5 = howard(G['n6'], G['U'][idx], G['V'][idx], w5)
        res['lam5'] = Fr(int(w5[c5].sum()), len(c5))
        wit = ub6[G['K6'][idx]] < INF
        res['ceiling'] = None
        if wit.any():
            sidx = idx[wit]
            m = k6loop.prune(G['n6'], G['U'][sidx], G['V'][sidx])
            sidx = sidx[m]
            if len(sidx):
                wc = ub6[G['K6'][sidx]]
                _, cc = howard(G['n6'], G['U'][sidx], G['V'][sidx], wc)
                res['ceiling'] = Fr(int(wc[cc].sum()), len(cc))
                res['ceil_keys'] = [keystr(G['keys6'][G['K6'][sidx[e]]]) for e in cc]
    return res


def main():
    hours = float(sys.argv[1])
    delta = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    sample = int(sys.argv[3]) if len(sys.argv) > 3 else 25
    os.makedirs(SCR, exist_ok=True)
    G, P, O, sub = setup()
    Tb = Tables(G, sub)
    print('tables', len(Tb.k5), 'five-keys (extended)', 'rss', round(rss_mb()), flush=True)
    t_end = time.time() + 3600 * hours
    rnd = 0
    if os.path.exists(ROUNDS):
        rnd = sum(1 for _ in open(ROUNDS))
    while True:
        t = time.time()
        r = evaluate(G, P, O, Tb, extra=(rnd % 10 == 0))
        lam = r['lam6']; cyc = r['cyc']
        ks6 = [int(G['K6'][e]) for e in cyc]
        rec = dict(round=rnd, time=time.strftime('%H:%M:%S'), lam6=str(lam), mu6=round(float(lam) / 6, 3),
                   m=round(mbound(float(lam) / 6), 3), len=len(cyc), live=len(r['idx']), eval_s=round(time.time() - t, 1),
                   rss=round(rss_mb()), calls=sum(1 for _ in open(OW)) if os.path.exists(OW) else 0,
                   cycle=[[keystr(G['keys6'][j]), int(r['W6'][j]), P.st.get(G['keys6'][j])] for j in ks6])
        if 'lam5' in r:
            rec['mu5'] = round(float(r['lam5']) / 5, 3)
            rec['ceiling_mu6'] = r['ceiling'] and round(float(r['ceiling']) / 6, 3)
            rec['ceiling_m'] = r['ceiling'] and round(mbound(float(r['ceiling']) / 6), 3)
            rec['ceiling_lam6'] = r['ceiling'] and str(r['ceiling'])
            rec['ceiling_keys'] = r.get('ceil_keys')
        print(json.dumps({k: v for k, v in rec.items() if k != 'cycle'}), flush=True)
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if time.time() > t_end:
            break
        tgt = math.ceil(float(lam)) + delta
        W6 = r['W6']; lb5 = r['lb5']
        # bulk plain phase: the BULK plain-untested live 6-keys of lowest weight (cheap, mostly UNSAT)
        ks = np.unique(G['K6'][r['idx']])
        unk = [j for j in ks[np.argsort(W6[ks], kind='stable')] if P.st.get(G['keys6'][j]) is None]
        cyc_unk = [j for j in dict.fromkeys(ks6) if P.st.get(G['keys6'][j]) is None]
        nb = Counter()
        groups = {}
        for j in unk:
            ds, al = G['keys6'][j]
            groups.setdefault((ds, al[1:]), []).append(G['keys6'][j])
        for j in cyc_unk + unk[:BULK]:
            if time.time() > t_end:
                break
            k6 = G['keys6'][j]
            if P.st.get(k6) is not None:
                continue
            mem = [k for k in groups.get((k6[0], k6[1][1:]), []) if P.st.get(k) is None]
            if RANGE and len(mem) >= 2:
                rr = range_test(P, mem)
                nb['range_' + rr] += 1
                if rr == 'UNSAT':
                    nb['UNSAT'] += len(mem)
                    continue
            nb[P.test(k6, 20)['result']] += 1
        if nb:
            print(f'   bulk plain: {dict(nb)}; untested below lam+{delta}: {sum(1 for j in unk if W6[j] < tgt)}', flush=True)
        if cyc_unk:
            rnd += 1
            continue                 # re-evaluate before spending threshold tests on this cycle
        done = set()
        for j in sorted(set(ks6), key=lambda j: W6[j]):
            if time.time() > t_end:
                break
            k6 = G['keys6'][j]
            if P.st.get(k6) is None:
                pr = P.test(k6, 60)
                print(f'   6w plain {keystr(k6)}: {pr["result"]} {pr["seconds"]}s', flush=True)
                if pr['result'] == 'UNSAT':
                    continue
            ok = False
            opts = []
            for i5, s in ((Tb.L[j], Tb.sL[j]), (Tb.R[j], Tb.sF[j])):
                k5 = Tb.k5[i5]
                need = tgt - int(s)
                st = O.get(k5)
                cur = max(st['lb'], int(Tb.floor5[i5]))
                if cur >= need:
                    ok = True; break
                if P.blocked(k5) or (st['ub'] is not None and st['ub'] < need) or \
                        (st['fail'] is not None and st['fail'] <= need):
                    continue
                opts.append((need, k5))
            if ok:
                continue
            for need, k5 in sorted(opts, key=lambda x: x[0]):
                if k5 in done:
                    if max(O.get(k5)['lb'], 0) >= need:
                        ok = True; break
                    continue
                done.add(k5)
                T0 = 10 * math.ceil(need / 10)
                res = ladder(k5, [T0 + 10 * i for i in range(5)], TL5, O, sample)
                print(f'   5w {keystr(k5)} need {need}: {res}', flush=True)
                if O.get(k5)['lb'] >= need:
                    ok = True; break
            if ok:
                continue
            st6 = O.get(k6)
            hi = min(st6['ub'] if st6['ub'] is not None else INF, st6['fail'] - 1 if st6['fail'] is not None else INF)
            if hi <= W6[j] or (st6['fail'] is not None and st6['fail'] - W6[j] <= 2):
                print(f'   6w {keystr(k6)} capped: lb {st6["lb"]} ub {st6["ub"]} fail {st6["fail"]}', flush=True)
                continue
            T0 = 10 * math.ceil(tgt / 10)
            if st6['fail'] is not None and st6['fail'] <= T0:      # below a timeout: halfway
                T0 = (int(W6[j]) + st6['fail'] + 1) // 2
            Ts = sorted({min(T0 + 10 * i, hi) for i in range(4)})
            res = ladder(k6, Ts, TL6, O, sample)
            print(f'   6w {keystr(k6)} tgt {tgt}: {res}', flush=True)
        rnd += 1


if __name__ == '__main__':
    main()
