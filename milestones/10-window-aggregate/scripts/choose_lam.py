"""Choose the mean p/q for a Lean chain: the smallest denominator whose Bellman-Ford potential
gives the target bound and fits the 8-bit SWAR fields (P + R <= 128, NS * Q + R < 128).

    python choose_lam.py --L 7 --k 6 --K 7 --avoid ../data/avoid_k6.json --escalate 4 --target 232

Only fractions not above the minimum cycle mean are tried (Bellman-Ford then terminates).
"""
import argparse, json, time
from fractions import Fraction as Fr
import numpy as np
from refine import Oracle
from refine_fast import FastAutomaton, prune, bellman_ford
from howard_fast import min_cycle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=7)
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--escalate', type=int, default=None)
    ap.add_argument('--avoid')
    ap.add_argument('--target', type=int, required=True)
    ap.add_argument('--qmax', type=int, default=12)
    a = ap.parse_args()
    if a.escalate:
        from refine import TwoLevelOracle
        O = TwoLevelOracle(a.radius, a.escalate)
    else:
        O = Oracle(a.radius)
    if a.avoid:
        for e in json.load(open(a.avoid)):
            O.known[(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))] = 'AVOID'
    A = FastAutomaton(a.L, a.k, a.K)
    NS = a.K + 1
    U, V, W, EXT = A.edges(O)
    m = prune(A.n, U, V); idx = np.nonzero(m)[0]
    mu, cyc = min_cycle(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
    lam_min = Fr(int(W[cyc].sum()), len(cyc))
    print('minimum mean', lam_min, float(lam_min), flush=True)
    cands = sorted({Fr(p, q) for q in range(1, a.qmax + 1) for p in range(4 * q, 6 * q + 1)
                    if Fr(p, q) <= lam_min}, key=lambda f: (f.denominator, -f))
    best = None
    for lam in cands:
        P, Q = lam.numerator, lam.denominator
        # necessary: 1010 Q + R < 226 P for the target 232 (general form below) with R >= 0
        C0 = P * a.L - Q * (a.L - 1)
        if (9179 * Q + C0 - 8 * Q) // (P + 35 * Q) > a.target:
            continue
        t = time.time()
        pi = bellman_ford(A.n, U, V, W, P, Q)
        R = int(pi.max() - pi.min())
        B = (9179 * Q + C0 + R - 8 * Q) // (P + 35 * Q)
        fits = P + R <= 128 and NS * Q + R < 128
        print(f'{lam} ({float(lam):.4f}): range {R}, bound {B}, fits {fits} [{time.time()-t:.0f}s]', flush=True)
        if B <= a.target and fits:
            best = lam
            break
    print(json.dumps({'minimum_mean': str(lam_min), 'chosen': str(best) if best else None}))


if __name__ == '__main__':
    main()
