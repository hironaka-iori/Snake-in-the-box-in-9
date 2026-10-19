"""Lazy selection of window exclusions for a target bound (an alternative to minimize_fast).

minimize_fast fixes one potential for the full set of refuted windows and then drops every
window that potential does not need.  Here the potential stays free: start from the windows
that are already certified, find minimum-mean cycles of the automaton they leave (C Howard,
many near-minimal cycles per round), and break each cycle with the cheapest refuted window on
it (oracle seconds, which predict certification time well), until the minimum mean reaches the
target and the smallest start constant D gives the target bound.  Only windows refuted by the
oracle are added, so the result needs certificates for the added windows only.

  python lazy_select.py --index ../data/direction_certificates_k6.json --lam 9/2 --bound 232 --tag _lazy
"""
import argparse, json, os, time
from collections import Counter
from fractions import Fraction as Fr
import numpy as np
from refine import DATA, TwoLevelOracle
from refine_fast import FastAutomaton, prune
from howard_fast import HowardGraph


class Known:
    def __init__(self, keys):
        self.known = {k: 'UNSAT' for k in keys}

    def status(self, k):
        return self.known.get(k)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=7)
    ap.add_argument('--k', type=int, default=6)
    ap.add_argument('--K', type=int, default=7)
    ap.add_argument('--index', required=True)
    ap.add_argument('--avoid', default=os.path.join(DATA, 'avoid_k6.json'))
    ap.add_argument('--lam', required=True)
    ap.add_argument('--bound', type=int, required=True)
    ap.add_argument('--batch', type=int, default=300)
    ap.add_argument('--slack', type=float, default=0.3)
    ap.add_argument('--budget', type=float, default=120.0)
    ap.add_argument('--tag', default='_lazy')
    a = ap.parse_args()
    target = Fr(a.lam); P, Q = target.numerator, target.denominator
    A = FastAutomaton(a.L, a.k, a.K)
    O = TwoLevelOracle(3, 4)
    avoid = {(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha'])) for e in json.load(open(a.avoid))}
    pool = {k for k, st in O.known.items() if st == 'UNSAT' and k not in avoid}
    cost = {}
    import glob
    for path in sorted(glob.glob(os.path.join(DATA, 'oracle_cache*.jsonl'))):
        for line in open(path):
            try:
                e = json.loads(line)
            except ValueError:
                continue
            if e.get('status') == 'UNSAT' and 'alpha' in e:
                k2 = (tuple(e['dirs']), tuple(map(tuple, e['alpha'])))
                cost[k2] = min(cost.get(k2, 1e9), float(e.get('seconds', 1.0)))
    cert = {(tuple(c['dirs']), tuple(map(tuple, c['alpha']))) for c in json.load(open(a.index))['cases']
            if c['drat_trim_verified']}
    sel = set(cert)
    added = set()
    print('certified', len(cert), 'pool', len(pool), flush=True)
    prefer = None
    for rnd in range(1000):
        t = time.time()
        K = Known(sel)
        U, V, W, EXT = A.edges(K)
        m = prune(A.n, U, V); idx = np.nonzero(m)[0]
        G = HowardGraph(A.n, U[idx], V[idx], W[idx], prefer=prefer)
        mu, cyc = G.solve(); prefer = G.successors()
        cyc = [idx[e] for e in cyc]
        exact = Fr(int(W[cyc].sum()), len(cyc))
        if exact >= target:
            from min_range import min_start_potential, init_sums
            D, pi = min_start_potential(A, U, V, W, P, Q, 300)
            C = P * a.L - Q * (a.L - a.k) + D
            B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
            print(f'round {rnd}: mean {exact} reached; D {D} bound {B}', flush=True)
            if B <= a.bound:
                break
            # the start constant is too large: keep breaking the cycles closest to the target
        batch = [cyc] + [[idx[e] for e in c] for m_, c in G.cycles(a.batch, max(mu, float(target)) + a.slack,
                                                                    budget=a.budget)[1:]]
        cyc_wins = []
        for c in batch:
            cw = set()
            for e in c:
                ds, al = A.decode(U[e], EXT[e], W[e])
                for cc in range(2, a.k + 1):
                    cw.add(A.window_key(tuple(ds[-(cc + 1):]), tuple(al[-cc:])))
            cyc_wins.append(cw)
        # greedy cover: windows of the pool on many cycles and cheap to certify first
        freq = Counter(w for cw in cyc_wins for w in cw if w in pool and w not in sel)
        new = set()
        for cw in sorted(cyc_wins, key=len):
            if cw & sel or cw & new:
                continue
            cand = [w for w in cw if w in pool and w not in sel]
            if not cand:
                continue                      # a cycle no refuted window breaks: the target is out of reach here
            new.add(min(cand, key=lambda w: (cost.get(w, 1.0) + 0.05) / freq[w]))
        if not new:
            print(f'round {rnd}: mean {exact}, no refuted window breaks the cycles; stop', flush=True)
            break
        sel |= new; added |= new
        print(f'round {rnd}: mean {exact} ({mu:.4f}) cycles {len(batch)} added {len(new)} total added {len(added)} '
              f'est. oracle s {sum(cost.get(w, 1.0) for w in added):.0f} [{time.time() - t:.0f}s]', flush=True)
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'lambda': str(target), 'bound': a.bound,
           'certified_used': len(cert), 'added': len(added),
           'exclusions': [{'dirs': list(x[0]), 'alpha': [list(r) for r in x[1]], 'radius': O.level(x) or 3}
                          for x in sorted(sel)]}
    path = os.path.join(DATA, f'minimal_L{a.L}_k{a.k}_K{a.K}_r3{a.tag}.json')
    json.dump(out, open(path, 'w'), indent=1)
    print('wrote', path, 'added', len(added))


if __name__ == '__main__':
    main()
