"""Potential-guided bulk tests for the share-weighted k6 product (runs next to loop.py).

Optimistic share S5opt = max(lb, min(ub, F, fail - 1)) (what the window could still be proved to
carry); Bellman-Ford from 0 for Q (120 A + S5opt) - P at the target lambda_t = P/Q on every allowed
transition gives a potential pi (if lambda_t is below the optimistic minimum).  Transitions whose
PROVED weight violates pi,
    Q (120 A + S5lb) - P + pi(u) - pi(v) < 0,
are the remaining work for a chain at lambda_t with this potential.  They are processed in order of
the deficit: plain test of the 6-window if unknown, plain test of the 5-window if never solved,
then one share threshold at the smallest level >= the deficit (<= ub).  Every BATCH tests the
potential is recomputed.  Results go to data/oracle_plain_bulk.jsonl and oracle_share_bulk.jsonl,
which loop.py and comb.py also read.
usage: nice -n 10 python bulk.py HOURS P/Q [F] [TL]
"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import solvers as SV
import loop as LP

SV.OPL = os.path.join(HERE, 'data', 'oracle_plain_bulk.jsonl')
SV.OSH = os.path.join(HERE, 'data', 'oracle_share_bulk.jsonl')
INF = 10 ** 6
LEVELS = [16, 24, 32, 48, 72, 108, 150, 200, 260]
BATCH = 400
LOG = os.path.join(HERE, 'data', 'bulk_rounds.jsonl')


def share_arrays(st):
    """Per transition: ub, fail of its trailing 5-window (via the 5-key of each transition)."""
    ub = np.full(len(st.G['U']), INF, np.int64); fail = np.full(len(st.G['U']), INF, np.int64)
    for k, s in st.O.st.items():
        if len(k[1]) != 5 or (s['ub'] >= INF and s['fail'] >= INF):
            continue
        for t in C.itertools.product(*[C.lumped_choices(a) for a in k[1]]):
            lk = C.fp.lkey(k[0], t)
            p = st.positions(lk)
            ub[p] = np.minimum(ub[p], s['ub']); fail[p] = np.minimum(fail[p], s['fail'])
    return ub, fail


def main():
    hours = float(sys.argv[1]); lam = Fr(sys.argv[2])
    F = int(sys.argv[3]) if len(sys.argv) > 3 else 108
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else 60
    P, Q = lam.numerator, lam.denominator
    st = LP.State()
    t_end = time.time() + hours * 3600
    it = 0
    while time.time() < t_end:
        t0 = time.time()
        ub, fail = share_arrays(st)
        A = st.G['A'].astype(np.int64); lb = st.G['S5'].astype(np.int64)
        opt = np.maximum(lb, np.minimum(np.minimum(ub, F), fail - 1))
        idx = np.nonzero(st.ok)[0]
        U = st.G['U'][idx].astype(np.int64); V = st.G['V'][idx].astype(np.int64)
        pi, rounds = C.bellman_ford(int(st.G['n']), U, V, Q * (120 * A[idx] + opt[idx]) - P, 3000)
        rec = dict(it=it, time=time.strftime('%H:%M:%S'), lam_t=str(lam), F=F, bf_rounds=rounds,
                   feasible=pi is not None)
        if pi is None:
            lamc, cyc, nlive = st.evaluate()
            rec.update(note='lambda_t above the optimistic minimum', lam_lo=str(lamc))
            C.log(json.dumps(rec))
            with open(LOG, 'a') as f:
                f.write(json.dumps(rec) + '\n')
            break
        red = Q * (120 * A[idx] + lb[idx]) - P + pi[U] - pi[V]
        bad = np.nonzero(red < 0)[0]
        order = bad[np.argsort(red[bad])]
        need = -(-(P - Q * 120 * A[idx[order]] - pi[U[order]] + pi[V[order]]) // Q)
        rec.update(deficient=int(len(bad)), R=int(pi.max() - pi.min()))
        C.log(f"bulk it {it}: deficient {len(bad)} transitions, BF {rounds} rounds, R {rec['R']}")
        done = set(); tests = 0; stats = {}
        for e, T in zip(idx[order], need):
            if tests >= BATCH or time.time() > t_end:
                break
            ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
            if (k5, k6) in done or not st.ok[e]:
                continue
            done.add((k5, k6))
            if st.S.st.get(k6) is None:
                r = SV.plain(k6, tl=tl / 2); tests += 1
                st.S.st[k6] = r['result']; stats['p6_' + r['result']] = stats.get('p6_' + r['result'], 0) + 1
                if r['result'] == 'UNSAT':
                    st.exclude(k6); continue
            if st.S.st.get(k5) == 'UNSAT':
                st.exclude(k5); continue
            s = st.share_state(k5)
            if not s.get('tested') and st.S.st.get(k5) is None:
                r = SV.plain(k5, tl=tl / 2); tests += 1
                st.S.st[k5] = r['result']; stats['p5_' + r['result']] = stats.get('p5_' + r['result'], 0) + 1
                if r['result'] == 'UNSAT':
                    st.exclude(k5); continue
                if r['result'] == 'SAT':
                    st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
            if st.G['S5'][e] >= T:
                continue
            Tt = next((L for L in LEVELS if L >= T), None)
            if Tt is None or Tt > s['ub'] or Tt >= s['fail'] or Tt <= s['lb']:
                Tt = min(int(T), s['ub']) if T <= s['ub'] and T < s['fail'] and T > s['lb'] else None
            if Tt is None:
                stats['skip'] = stats.get('skip', 0) + 1
                continue
            r = SV.share_thr(k5, int(Tt), tl=tl); tests += 1
            stats['t_' + r['result']] = stats.get('t_' + r['result'], 0) + 1
            LP.apply_share(st, k5, r)
        lamc, cyc, nlive = st.evaluate()
        rec.update(tests=tests, stats=stats, lam_lo=str(lamc), mu_lo=float(lamc) / 120,
                   m_real=C.bound_real(float(lamc), 1, 0, 0), s=round(time.time() - t0))
        C.log(json.dumps(rec))
        with open(LOG, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        it += 1
        if tests == 0:
            break


if __name__ == '__main__':
    main()
