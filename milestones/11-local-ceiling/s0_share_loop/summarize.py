"""Summary of a refine_share.py run: progress, certificate counts, proof-size samples, cost
estimate, and NON-rigorous what-if means (untested windows assumed to force F).
usage: summarize.py [--whatif 0,48,72,96,108] > summary.json"""
import argparse, json, os, sys
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
import refine_share as R
from refine import howard, prune

KERNEL_S_PER_HINT = 34.0 * 3600 / 289e6      # the 237 replay: 289 M hints, 34 kernel-hours


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--whatif', default='0,48,72,96,108')
    a = ap.parse_args()
    n, U, V, S, KI, keys = R.load_compact(R.DEFAULT_PKL)
    O = R.ShareOracle()
    rounds = [json.loads(l) for l in open(R.ROUNDS)]
    calls = [json.loads(l) for l in open(R.ORACLE)]
    out = {'rounds': len(rounds), 'first': {k: rounds[0][k] for k in ('mu_lo', 'm_lo', 'mu_hi', 'm_hi')},
           'last': {k: rounds[-1][k] for k in ('round', 'lam_lo', 'mu_lo', 'm_lo', 'lam_hi', 'mu_hi', 'm_hi', 'cycle_lo', 'cycle_lo_T5')},
           'progress': [(r['round'], r['time'], r['mu_lo'], r['mu_hi']) for r in rounds]}
    # certificate counts on the automaton
    used = set(int(x) for x in np.unique(KI))
    st = [O.st.get(keys[i]) for i in used]
    out['keys_on_automaton'] = len(used)
    out['share_certs_lb_gt0'] = sum(1 for s in st if s and s['lb'] > 0 and not s['excl'])
    out['plain_exclusions_new'] = sum(1 for s in st if s and s['excl'])
    out['tested'] = sum(1 for s in st if s and s['tested'])
    out['lb_hist'] = {}
    for s in st:
        if s and s['lb'] > 0 and not s['excl']:
            out['lb_hist'][s['lb']] = out['lb_hist'].get(s['lb'], 0) + 1
    out['ub_below_108'] = sum(1 for s in st if s and s['ub'] < 108)
    # solver calls
    from collections import Counter
    out['calls'] = {f'{k}:{v}': c for (k, v), c in Counter((r['kind'], r['result']) for r in calls).items()}
    th = [r for r in calls if r['kind'] == 'thr']
    secs = sorted(r['seconds'] for r in th)
    if secs:
        out['thr_seconds'] = dict(median=secs[len(secs) // 2], p90=secs[int(len(secs) * .9)], max=secs[-1],
                                  total_h=round(sum(secs) / 3600, 2))
    pr = [r['proof'] | {'T': r['T'], 'seconds': r['seconds']} for r in calls if 'proof' in r and 'lrat_hints' in r['proof']]
    if pr:
        h = sorted(p['lrat_hints'] for p in pr)
        out['proof_samples'] = [{k: p.get(k) for k in ('T', 'seconds', 'variables', 'clauses', 'drat_bytes', 'drat_lines',
                                                       'drat_seconds', 'lrat_hints', 'lrat_lemmas', 'core_clauses')} for p in pr]
        out['hints'] = dict(n=len(h), median=h[len(h) // 2], mean=int(sum(h) / len(h)), max=h[-1], min=h[0])
        nc = out['share_certs_lb_gt0']
        out['cost_estimate'] = dict(
            certs=nc, hints_total_est=int(nc * sum(h) / len(h)),
            kernel_hours_est=round(nc * sum(h) / len(h) * KERNEL_S_PER_HINT / 3600, 1),
            kernel_hours_median_based=round(nc * h[len(h) // 2] * KERNEL_S_PER_HINT / 3600, 1),
            drat_mb_mean=round(sum(p['drat_bytes'] for p in pr) / len(pr) / 1e6, 1))
    # what-if means (NOT rigorous): untested windows assumed T5 = F; tested windows use lb
    lb = np.array([O.st[k]['lb'] if k in O.st else 0 for k in keys], np.int64)
    tested = np.array([O.st[k]['tested'] if k in O.st else False for k in keys], bool)
    ub = np.array([O.st[k]['ub'] if k in O.st else R.INF for k in keys], np.int64)
    ex = np.array([O.st[k]['excl'] if k in O.st else False for k in keys], bool)
    keep = ~ex[KI]; m = prune(n, U[keep], V[keep]); idx = np.nonzero(keep)[0][m]
    U2, V2, K2, S2 = U[idx], V[idx], KI[idx], S[idx].astype(np.int64)
    wi = []
    for F in [int(x) for x in a.whatif.split(',')]:
        for mode in ('lb', 'opt'):
            T5 = np.where(tested, lb if mode == 'lb' else np.minimum(ub, np.maximum(lb, F)), F)
            w = R.UNIT * S2 + T5[K2]
            _, cyc = howard(n, U2, V2, w)
            lam = Fr(int(w[cyc].sum()), len(cyc)); mu = float(lam) / R.UNIT
            wi.append(dict(F=F, tested=mode, mu=round(mu, 4), m_le=round(R.bound_m(mu), 2), len=len(cyc),
                           untested_on_cycle=int(sum(1 for e in cyc if not tested[K2[e]]))))
            print(json.dumps(wi[-1]), file=sys.stderr, flush=True)
    out['whatif'] = wi
    print(json.dumps(out, indent=1))


if __name__ == '__main__':
    main()
