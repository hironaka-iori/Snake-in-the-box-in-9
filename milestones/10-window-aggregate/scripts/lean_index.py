"""Index check on LeanAutomaton's CSR arrays: the memory-lean `refine_fast.py --index --start`.

Rebuilds the direction automaton from the drat-trim-verified entries of a certificate index only
(optionally: only those of a window set, which must then be certified completely, --require-set),
computes the exact minimum cycle mean (prune + C Howard, lean_minimize.Graph.min_mean), and at the
mean --lam (<= the minimum; default the minimum) the smallest start-bounded potential
0 <= pi <= D + Q * (symbol sum of the state), checked on every edge in C (leanmin_c.check_pot); then
the walk bound (refine_fast.vertex_bound's dynamic programme, lean_minimize.vertex_bound).

Output fields follow refine_fast.py --index --start (direction_bound_L7_k6_K7_r34.json):
  start_potential_bound_edges = (9179 Q + C - 8 Q) // (P + 35 Q),  C = P L - Q (L - k) + D.
Exits 2 (and writes no output file) when the minimum mean is below --lam.

Share weights (share_lb.py): --lb FILE uses the entries marked "certified": true (a checked refutation of
"shares <= lb - 1" for that window) as edge weights den * symbol + LB units, den = 21 k (--den); --lam,
min_mean and the potential are then in 1/den alpha units and
  start_potential_bound_edges = (9179 Q den - 8 Q den + P L - Q den (L - k) + D) // (P + 35 Q den).

  python lean_index.py --L 8 --k 7 --K 7 --index ../data/direction_certificates_k6.json \
      --set ../data/minimal_L8_k7_K7_r3_89_19.json --require-set --lam 89/19 \
      --out ../data/direction_bound_L8_k7_K7_89_19.json
"""
import argparse, json, os, sys, time
from fractions import Fraction as Fr
import numpy as np

SCRIPTS = os.path.dirname(os.path.abspath(__file__))
if SCRIPTS not in sys.path:
    sys.path.insert(0, SCRIPTS)
import share_lb                                                   # noqa: E402
from lean_automaton import LeanAutomaton                          # noqa: E402
from lean_minimize import (Graph, min_start_potential, start_constant, vertex_bound, init_digs,  # noqa: E402
                           _load, rss_mb)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', type=int, required=True)
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--K', type=int, required=True)
    ap.add_argument('--index', required=True, help='certificate index (only drat_trim_verified cases are used)')
    ap.add_argument('--set', help='use only the verified windows of this set (minimal_*.json)')
    ap.add_argument('--require-set', action='store_true', help='with --set: fail unless every window is verified')
    ap.add_argument('--lam', help='mean p/q of the start potential (<= the minimum mean; default the minimum)')
    ap.add_argument('--hi', type=int, default=300, help='upper end of the binary search over D')
    ap.add_argument('--no-vb', action='store_true', help='skip the walk bound')
    ap.add_argument('--lb', help='share lower bounds (jsonl); only entries with "certified": true are used')
    ap.add_argument('--lb-uncertified', action='store_true', help='with --lb: also uncertified entries (testing only)')
    ap.add_argument('--den', type=int, default=None, help='weight denominator (default 21 k with --lb, else 1)')
    ap.add_argument('--out')
    a = ap.parse_args(argv)
    T0 = time.time()
    keys = {(tuple(c['dirs']), tuple(tuple(x) for x in c['alpha']))
            for c in json.load(open(a.index))['cases'] if c.get('drat_trim_verified')}
    out = {'L': a.L, 'k': a.k, 'K': a.K, 'index': os.path.basename(a.index), 'verified_in_index': len(keys)}
    if a.set:
        wanted = {(tuple(e['dirs']), tuple(tuple(x) for x in e['alpha']))
                  for e in json.load(open(a.set))['exclusions']}
        missing = len(wanted - keys)
        keys &= wanted
        out.update({'set': os.path.basename(a.set), 'set_windows': len(wanted), 'set_windows_not_verified': missing})
        print(f'set {a.set}: {len(wanted)} windows, {missing} not verified in the index', flush=True)
        if a.require_set and missing:
            sys.exit(f'{missing} windows of the set are not certified')
    out['listed_exclusions'] = len(keys)
    A = LeanAutomaton(a.L, a.k, a.K)
    den = a.den or (share_lb.unit(a.k) if a.lb else 1)
    if a.lb:
        tab = share_lb.ShareTable.load(a.lb, certified_only=not a.lb_uncertified)
        out.update({'share_lb_file': os.path.basename(a.lb), 'share_lb_windows': len(tab.lb),
                    'share_lb_certified_only': not a.lb_uncertified})
        A.set_weights(den, tab)
    else:
        A.set_weights(den)
    out['weight_denominator'] = den
    G = Graph(A, keys)
    out.update({'states': int(A.n), 'edges': int(G.E)})
    print(f'graph: {A.n} states, {G.E} edges ({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    mu = G.min_mean()
    out['min_mean'] = str(mu)
    print(f'minimum mean {mu} ({float(mu):.5f}) ({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    lam = Fr(a.lam) if a.lam else mu
    if lam > mu:
        print(json.dumps(out))
        print(f'FAILED: minimum mean {mu} < {lam}', flush=True)
        sys.exit(2)
    P, Q = lam.numerator, lam.denominator
    D, pi = min_start_potential(A, G, P, Q, a.hi, verbose=True)
    if pi is None:
        print(json.dumps(out))
        sys.exit(f'no start-bounded potential at {lam} with D <= {a.hi}')
    pi -= pi.min()
    D = start_constant(A, pi, Q)
    # the final potential, re-checked on every edge: reduced costs >= 0, 0 <= pi <= D + Q * symbol sum
    bad = _load(G.W.dtype).check_pot(G.n, G.starts, G.V, G.W, P, Q, pi, 1, int(D), init_digs(A), A.m1)
    assert bad == 0, f'{bad} violations of the start potential'
    out.update({'lambda': str(lam), 'start_constant_D': int(D), 'start_potential_range': int(pi.max()),
                'start_potential_checked_on_every_edge': True,
                'start_potential_bound_edges': share_lb.bound_edges(P, Q, a.L, a.k, int(D), den)})
    pi = None
    print(f'start potential at {lam}: D {D}, bound {out["start_potential_bound_edges"]} edges '
          f'({time.time() - T0:.0f}s, peak {rss_mb()} MB)', flush=True)
    if not a.no_vb:
        vb = vertex_bound(A, G)
        out.update({'max_vertices': vb, 'max_edges': None if vb is None else vb - 1})
        print(f'walk bound {vb} vertices ({time.time() - T0:.0f}s)', flush=True)
    print(json.dumps(out))
    if a.out:
        json.dump(out, open(a.out, 'w'), indent=1)
        print('wrote', a.out)
    print(f'total {time.time() - T0:.0f}s, peak RSS {rss_mb()} MB', flush=True)


if __name__ == '__main__':
    main()
