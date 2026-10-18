"""Direction-aware automaton over empty-square-aware weight buckets (omega_oracle.OmegaModel).

Symbols: b = min(floor(omega / 21), K + 1) with omega = 21 alpha + empty-square shares (see
omega_oracle.py); b >= 1 because alpha >= 1 at internal vertices.  Edge weight = b, so a
minimum cycle mean mu gives  sum_x b(x) >= mu * (m - L) - R  along the path and, with
sum_x omega(x) <= 21 (9214 - 35 v), the same arithmetic as the alpha-only chains.

States and transitions are those of refine_fast.FastAutomaton (shape of the last L directions,
last k-1 symbols); a window of c centres ending at the new vertex is excluded when the bucket
query (dirs, buckets) is INFEASIBLE at the chosen radius.  Answers are cached in
data/omega_cache_r{radius}.jsonl; timeouts count as feasible.

  python refine_omega.py --L 6 --k 4 --K 11 --radius 3 --workers 2
"""
import argparse, json, os, time
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np
from refine import canon, DATA
from refine_fast import FastAutomaton, prune, howard, bellman_ford, vertex_bound


def okey(ds, bs):
    f = (canon(ds), tuple(bs))
    r = (canon(tuple(reversed(ds))), tuple(reversed(bs)))
    return min(f, r)


class OmegaAutomaton(FastAutomaton):
    def window_key(self, ds, al):
        return okey(ds, al)

    def forb_tables(self, oracle):
        T = {}
        for (dirs, bs), st in oracle.known.items():
            if st != 'UNSAT':
                continue
            cc = len(bs)
            if cc < 2 or cc > self.k or any(b < 1 or b > self.ns for b in bs):
                continue
            code = 0
            for b in bs:
                code = code * self.ns + (b - 1)
            T.setdefault(dirs, np.zeros(self.ns ** cc, bool))[code] = True
        return T


def _solve(arg):
    (ds, bs), radius, cap, limit = arg
    from omega_oracle import OmegaModel
    t = time.time()
    M = OmegaModel(list(ds), radius)
    M.constrain_buckets(list(bs), cap)
    st, _, cuts = M.decide(limit)
    return (ds, bs), st, round(time.time() - t, 2), cuts


class OmegaOracle:
    def __init__(self, radius, cap, limit):
        self.radius, self.cap, self.limit = radius, cap, limit
        self.path = os.path.join(DATA, f'omega_cache_r{radius}.jsonl')      # not oracle_cache*: refine.Oracle globs those
        self.known = {}
        if os.path.exists(self.path):
            for line in open(self.path):
                try:
                    e = json.loads(line)
                except ValueError:
                    continue
                if e['cap'] == cap:
                    self.known[(tuple(e['dirs']), tuple(e['buckets']))] = e['status']

    def status(self, k):
        return self.known.get(k)

    def query(self, keys, workers):
        keys = [k for k in dict.fromkeys(keys) if k not in self.known]
        if not keys:
            return 0
        with Pool(workers) as p:
            res = p.map(_solve, [(k, self.radius, self.cap, self.limit) for k in keys])
        with open(self.path, 'a', buffering=1) as f:
            for k, st, secs, cuts in res:
                self.known[k] = st
                f.write(json.dumps({'dirs': list(k[0]), 'buckets': list(k[1]), 'cap': self.cap, 'radius': self.radius,
                                    'status': st, 'seconds': secs, 'cuts': cuts}) + '\n')
        return len(keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, default=6)
    ap.add_argument('--k', type=int, default=4)
    ap.add_argument('--K', type=int, default=11, help='symbols 1..K exact buckets, K+1 = bucket >= K+1')
    ap.add_argument('--radius', type=int, default=3)
    ap.add_argument('--rounds', type=int, default=400)
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--slack', type=float, default=0.3)
    ap.add_argument('--batch', type=int, default=200)
    ap.add_argument('--query-timeout', type=float, default=60.0)
    a = ap.parse_args()
    cap = a.K + 1
    O = OmegaOracle(a.radius, cap, a.query_timeout)
    A = OmegaAutomaton(a.L, a.k, a.K)
    print('shapes', len(A.shapes), 'states', A.n, 'extensions', len(A.ext), 'cached', len(O.known), flush=True)
    log = []
    for rnd in range(a.rounds):
        t = time.time()
        U, V, W, EXT = A.edges(O)
        m = prune(A.n, U, V); idx = np.nonzero(m)[0]
        mu, cyc = howard(A.n, U[idx], V[idx], W[idx]); cyc = [idx[e] for e in cyc]
        exact = Fr(int(W[cyc].sum()), len(cyc))
        wins = []
        batch = [c for m_, c in howard.extra if m_ <= mu + a.slack][:a.batch]
        for cyc2 in [cyc] + batch:
            for e in cyc2:
                e = idx[e] if cyc2 is not cyc else e
                ds, bs = A.decode(U[e], EXT[e], W[e])
                for cc in range(2, a.k + 1):
                    wins.append(A.window_key(tuple(ds[-(cc + 1):]), tuple(bs[-cc:])))
        wins = list(dict.fromkeys(wins))
        newq = O.query(wins, a.workers)
        unsat = [x for x in wins if O.status(x) == 'UNSAT']
        print(f'round {rnd}: edges {len(idx)} mean {exact} ({mu:.4f}) cycle {[int(x) for x in W[cyc]]} '
              f'queried {newq} unsat-on-cycle {len(unsat)} [{time.time()-t:.0f}s]', flush=True)
        log.append({'round': rnd, 'mean': str(exact), 'cycle': [int(x) for x in W[cyc]], 'queried': newq, 'killed': len(unsat)})
        if not unsat:
            break
    pi = bellman_ford(A.n, U, V, W, exact.numerator, exact.denominator)
    vb = vertex_bound(A, U, V, W)
    R = int(pi.max() - pi.min()) if pi is not None else None
    P, Q = exact.numerator, exact.denominator
    C = P * a.L - Q * (a.L - 1) + (R if R is not None else 15)
    B = (9179 * Q + C - 8 * Q) // (P + 35 * Q)
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'radius': a.radius, 'weight': 'omega/21 buckets', 'min_mean': str(exact),
           'potential_range': R, 'potential_bound_edges': B, 'dp_bound_edges': vb - 1 if vb else None,
           'edges': int(len(U)), 'final_cycle': [int(x) for x in W[cyc]], 'rounds': log}
    json.dump(out, open(os.path.join(DATA, f'refine_omega_L{a.L}_k{a.k}_K{a.K}_r{a.radius}.json'), 'w'), indent=1)
    print(json.dumps({k2: v for k2, v in out.items() if k2 != 'rounds'}))


if __name__ == '__main__':
    main()
