"""Evaluate the w_3-charge automaton from the current oracle: rigorous mean (lo, with an exact
integer potential), ceiling (hi), what-if means, the binding windows and the final arithmetic.

Final arithmetic (see README): with lambda = P/Q the lo min cycle mean of T5 and R the range of
an integer potential for the weights Q*T5 - P,
    5 sum_{j=1}^{m-1} c(x_j) >= sum_{j=1}^{m-5} T5(W_j) + 20*257 >= (P (m-7) - R)/Q + 5140
(the windows W_3..W_{m-5} are the edges of an automaton walk -- the state needs seven directions
-- and W_1, W_2 are dropped), and  sum_{j=1}^{m-1} c(x_j) <= 64512 - 2*168 = 64176,  so
    m <= 7 + (Q (320880 - 5140) + R) / P = 7 + (315740 Q + R) / P.
usage: eval_w3.py [--whatif F ...]
"""
import argparse, json, os, sys
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_w3 as R
from refine import howard, exact_check

OUT = os.path.join(HERE, 'data', 'w3_eval.json')


def final_m(P, Q, Rg):
    return 7 + (315740 * Q + Rg) / P


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--whatif', type=int, nargs='*', default=[1400, 1420])
    ap.add_argument('--no-potential', action='store_true')
    a = ap.parse_args()
    n, U, V, S, KI, keys = R.load_compact()
    sub = R.Sub(); O = R.W3Oracle()
    fl = np.array([sub.floor5(k) for k in keys], np.int64)
    lb = np.array([max(O.st[k]['lb'] if k in O.st else 0, f) for k, f in zip(keys, fl)], np.int64)
    ub = np.array([O.st[k]['ub'] if k in O.st else R.INF for k in keys], np.int64)
    tested = np.array([k in O.st for k in keys])
    out = dict(keys=len(keys), tested=int(tested.sum()),
               lb_from_threshold=int(sum(1 for k in keys if k in O.st and O.st[k]['lb'] > 0)),
               sat_witness=int((ub < R.INF).sum()),
               timeouts=int(sum(1 for k in keys if k in O.st and O.st[k]['fail'] < R.INF and O.st[k]['lb'] < O.st[k]['fail'])))

    def run(name, T5):
        w = T5[KI]
        _, cyc = howard(n, U, V, w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        rec = dict(lam=str(lam), per_vertex_c=float(lam) / 5, w3=float(lam) / 60,
                   m_le_approx=final_m(lam.numerator, lam.denominator, 0), len=len(cyc),
                   cycle=[[list(keys[KI[e]][0]), [x[0] for x in keys[KI[e]][1]], int(T5[KI[e]]),
                           int(lb[KI[e]]), int(ub[KI[e]]) if ub[KI[e]] < R.INF else None] for e in cyc])
        return rec, lam
    out['lo'], lam = run('lo', lb)
    if not a.no_potential:
        pi = exact_check(n, U, V, lb[KI], lam.numerator, lam.denominator)
        if pi is not None:
            Rg = int(pi.max() - pi.min())
            out['lo']['potential_range'] = Rg
            out['lo']['m_le_rigorous'] = final_m(lam.numerator, lam.denominator, Rg)
    out['hi'], _ = run('hi', ub)
    for F in a.whatif:
        # untested / unsettled keys assumed to force min(F, ub); settled keys keep max(lb, min(F, ub))
        T5 = np.maximum(lb, np.minimum(ub, F))
        out[f'whatif_{F}'], _ = run(f'whatif_{F}', T5)
        out[f'whatif_{F}'].pop('cycle')
    print(json.dumps({k: (v if not isinstance(v, dict) else {kk: vv for kk, vv in v.items() if kk != 'cycle'})
                      for k, v in out.items()}, indent=1))
    print('lo cycle:', out['lo']['cycle'])
    print('hi cycle:', out['hi']['cycle'])
    json.dump(out, open(OUT, 'w'), indent=1)


if __name__ == '__main__':
    main()
