"""Stage B: the best combination of the share identity and the 3-cube census on the k6 full product.

For integer weights a (share identity, which contains alpha) and b (w_3 census) the step weight is
w = a (120 A + S5) + b W6 (comb.py).  For fixed a, b the minimum cycle mean lambda(a, b) is concave and
piecewise linear in (a, b); the bound (*) of comb.py is a ratio, so we search the one free ratio
beta = b/a by golden section (the LP dual over y = (a, b), Lagrangian form), then verify the best
point exactly: rational lambda from the cycle, integer Bellman-Ford potential on ALL allowed
transitions of the full product (the Lean check enumerates every state), its range R, and the integer
bound (*).

usage: lp.py KEYS SHARE W3 [--out FILE]
   KEYS  = all | cert | <key file>        plain exclusions (all known solver UNSAT / Lean-replayed / file)
   SHARE = none | cert | all              share lower bounds (none / Lean floors on main / every oracle)
   W3    = 0 | 1                          use the w_3 census
"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C


def setup(keys, share, w3):
    G = C.build(keys, with_share=(share != 'none'), with_w3=bool(w3), certified_share=(share == 'cert'))
    L = C.live(G)
    return G, L


def evaluate(G, L, a, b, Wf=None):
    n = int(G['n'])
    w = C.weights(G, a, b, L) if Wf is None else Wf
    mu, cyc = C.howard(n, G['U'][L], G['V'][L], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    return lam, [int(L[e]) for e in cyc]


def search(G, L, use_w3, log=print):
    c1 = int(G['c1'])
    res = {}

    def f(beta):
        a, b = (1000, int(round(beta * 1000))) if beta < 1e6 else (0, 1000)
        if (a, b) not in res:
            lam, cyc = evaluate(G, L, a, b)
            res[(a, b)] = (lam, cyc, C.bound_real(float(lam), a, b, c1))
            log(f'  a={a} b={b}: lambda={float(lam):.4f} ({lam}) m<={res[(a, b)][2]:.4f} cycle {len(cyc)}')
        return res[(a, b)][2]
    f(0.0)
    if use_w3:
        grid = [0.0, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 1e9]
        vals = [f(x) for x in grid]
        i = int(np.argmin(vals))
        lo, hi = grid[max(0, i - 1)], grid[min(len(grid) - 2, i + 1)]
        g = (5 ** 0.5 - 1) / 2
        x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
        for _ in range(14):
            if f(x1) < f(x2):
                hi = x2; x2 = x1; x1 = hi - g * (hi - lo)
            else:
                lo = x1; x1 = x2; x2 = lo + g * (hi - lo)
    best = min(res.items(), key=lambda kv: kv[1][2])
    return best, res


def exact(G, a, b, lam, maxit=40000, log=print):
    """Integer BF on every allowed transition for weights Q w - P, with P/Q <= lam chosen to
    keep the bound; returns dict with the potential range and the integer bound (*)."""
    c1 = int(G['c1'])
    n = int(G['n'])
    w = C.weights(G, a, b)
    U = G['U'].astype(np.int64); V = G['V'].astype(np.int64)
    out = []
    for lam_try in (lam, lam - Fr(1, 4), lam - 1, lam - 4):
        if lam_try <= 0:
            continue
        P, Q = lam_try.numerator, lam_try.denominator
        t0 = time.time()
        pi, it = C.bellman_ford(n, U, V, Q * w - P, maxit)
        if pi is None:
            log(f'  BF lambda={lam_try}: no convergence in {it} rounds')
            continue
        R = int(pi.max() - pi.min())
        m = C.bound_m(P, Q, R, a, b, c1)
        rec = dict(P=P, Q=Q, lam=float(lam_try), R=R, R_alpha_units=R / Q / (120 * a) if a else None,
                   bf_rounds=it, bound=int(m), bf_s=round(time.time() - t0, 1),
                   slack_to_next=int((P + 4200 * a * Q) * (m + 1) - (Q * (1099800 * a + b * (387072 - 36 * c1)) + 7 * P + R)))
        log(f'  exact: {rec}')
        out.append(rec)
        if len(out) >= 1 and out[-1]['bound'] == min(o['bound'] for o in out):
            break
    return out


def main():
    keys, share, w3 = sys.argv[1], sys.argv[2], int(sys.argv[3])
    outp = sys.argv[sys.argv.index('--out') + 1] if '--out' in sys.argv else None
    t0 = time.time()
    G, L = setup(keys, share, w3)
    C.log(f'config keys={keys} share={share} w3={w3}: {len(G["U"])} allowed, {len(L)} live, c1={int(G["c1"])}')
    (ab, (lam, cyc, m)), res = search(G, L, bool(w3), log=C.log)
    a, b = ab
    C.log(f'best a={a} b={b} lambda={lam} m<={m:.4f}')
    ex = exact(G, a, b, lam, log=C.log)
    rec = dict(keys=keys, share=share, w3=w3, allowed=int(len(G['U'])), live=int(len(L)), c1=int(G['c1']),
               a=a, b=b, lam=str(lam), lam_float=float(lam), m_real=m, exact=ex,
               cycle=C.cycle_info(G, None, cyc),
               scan=[dict(a=k[0], b=k[1], lam=str(v[0]), m_real=v[2]) for k, v in sorted(res.items())],
               seconds=round(time.time() - t0))
    print(json.dumps({k: v for k, v in rec.items() if k not in ('cycle', 'scan')}), flush=True)
    for r in rec['cycle']:
        print('   ', r)
    if outp:
        json.dump(rec, open(outp, 'w'), indent=1)


if __name__ == '__main__':
    main()
