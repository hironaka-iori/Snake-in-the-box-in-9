"""Exact bound of the current data (Refinement toward 232): weight 120 A + S5 (5-window and context
share bounds), every known plain key; Howard's lambda on the live core, then integer Bellman-Ford on
ALL allowed transitions for Q w - P at lambda_t = P/Q <= lambda (lambda itself and a few round values
below it, which can have a smaller range R), and the arithmetic (*) of comb.py with a = 1, b = 0:
    (P + 4200 Q) m <= 1099800 Q + 7 P + R.
usage: eval232.py [--out file.json] [--keys keysfile.json.gz]
"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C


def exact_best(G, lam, log=C.log):
    n = int(G['n'])
    w = C.weights(G, 1, 0)
    U = G['U'].astype(np.int64); V = G['V'].astype(np.int64)
    cands = [lam] + [Fr(x, 4) for x in range(int(lam * 4), int(lam * 4) - 12, -1) if Fr(x, 4) < lam]
    out = []
    for lt in cands:
        P, Q = lt.numerator, lt.denominator
        pi, it = C.bellman_ford(n, U, V, Q * w - P, 40000)
        if pi is None:
            continue
        R = int(pi.max() - pi.min())
        m = int(C.bound_m(P, Q, R, 1, 0, 0))
        out.append(dict(P=P, Q=Q, lam=float(lt), R=R, R_alpha_units=R / Q / 120, bf_rounds=it, bound=m,
                        slack=int((P + 4200 * Q) * (m + 1) - (Q * 1099800 + 7 * P + R))))
        log(f'  lambda_t {lt} = {float(lt):.3f}: R {R} ({R / Q / 120:.2f} alpha), {it} rounds, bound {m}')
    return out


def main():
    outp = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    t0 = time.time()
    G = C.build('all', with_share=True, with_w3=False)
    L = C.live(G)
    w = C.weights(G, 1, 0, L)
    mu, cyc = C.howard(int(G['n']), G['U'][L], G['V'][L], w)
    cycG = [int(L[e]) for e in cyc]
    lam = Fr(int(w[cyc].sum()), len(cyc))
    C.log(f'lambda {lam} = {float(lam) / 120:.4f} alpha, m_real {C.bound_real(float(lam), 1, 0, 0):.3f}, cycle {len(cyc)}')
    ex = exact_best(G, lam)
    best = min(ex, key=lambda r: (r['bound'], -r['slack'])) if ex else None
    rec = dict(allowed=int(len(G['U'])), live=int(len(L)), lam=str(lam), lam_alpha=float(lam) / 120,
               m_real=C.bound_real(float(lam), 1, 0, 0), exact=ex, best=best,
               need_232=(121200 + (best['R'] / best['Q'] if best else 0)) / 226 / 120,
               cycle=C.cycle_info(G, None, cycG), seconds=round(time.time() - t0))
    print(json.dumps({k: v for k, v in rec.items() if k != 'cycle'}), flush=True)
    if outp:
        json.dump(rec, open(outp, 'w'), indent=0)


if __name__ == '__main__':
    main()
