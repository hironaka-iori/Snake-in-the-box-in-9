"""Drop expensive window exclusions while the Lean bound stays at the target.

minimize.py keeps the minimum cycle mean fixed.  The Lean bound only needs the
arithmetic of gen_lean_chain5.py to give the target: with minimum mean P/Q, potential
range R <= 2^bits - 1 and C = (2^bits - 1) + 7P - 6Q,

    (P + 35 Q) m <= 9171 Q + C,

so a slightly lower mean can still give the same bound.  Starting from a minimal set,
this script tries to drop its most expensive exclusions (proof lengths from
data/proof_cost_r<r>.jsonl), one at a time, most expensive first; a drop is kept when the
new minimum mean and potential still give the target through that arithmetic.

  python prune_costly.py --set ../data/minimal_L7_k5_K5_cost.json --target-edges 238 --tries 30
"""
import argparse, json, os
from fractions import Fraction as Fr
import numpy as np
from refine import Automaton, prune, howard, exact_check, DATA, key
from minimize import all_candidates, load_costs


def lean_bound(P, Q, bits):
    C = (1 << bits) - 1 + 7 * P - 6 * Q
    return (9171 * Q + C) // (P + 35 * Q)


def mean_and_potential(A, U, V, W):
    m = prune(A.n, U, V)
    idx = np.nonzero(m)[0]
    mu, cyc = howard(A.n, U[idx], V[idx], W[idx])
    cyc = [idx[e] for e in cyc]
    lam = Fr(int(W[cyc].sum()), len(cyc))
    pi = exact_check(A.n, U, V, W, lam.numerator, lam.denominator)
    return lam, pi


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--set', required=True)
    ap.add_argument('--target-edges', type=int, required=True)
    ap.add_argument('--tries', type=int, default=30)
    ap.add_argument('--bits', type=int, default=4, help='potential field width in Lean')
    ap.add_argument('--out', default=None)
    ap.add_argument('--hints-from', default=None,
                    help='use the LRAT hint counts of a lean_core summary (+ index) as costs where known')
    ap.add_argument('--index', default=None,
                    help='certificate index to filter to the kept exclusions (written next to --out as *_index.json)')
    ap.add_argument('--costs', default=None,
                    help='jsonl of costs overriding data/proof_cost_r<r>.jsonl (field proof_lines)')
    ap.add_argument('--first', nargs='*', default=[],
                    help='module names (e.g. D0120A334) to try first, in this order')
    a = ap.parse_args()
    spec = json.load(open(a.set))
    L, k, K, radius = spec['L'], spec['k'], spec['K'], spec.get('radius', 3)
    keep = {(tuple(e['dirs']), tuple(map(tuple, e['alpha']))) for e in spec['exclusions']}
    _, costs = load_costs(radius)
    if a.costs:   # e.g. estimated LRAT hints instead of DRUP lines (same jsonl format)
        for line in open(a.costs):
            e = json.loads(line)
            costs[(tuple(e['dirs']), tuple(map(tuple, e['alpha'])))] = e['proof_lines']
    first = []
    if a.hints_from:
        summ = json.load(open(os.path.join(a.hints_from, '_summary.json')))['per_case']
        for n, v in summ.items():
            meta = json.load(open(os.path.join(a.hints_from, n + '.json')))
            al = tuple((lo, hi) for lo, hi in meta['bounds'])
            kk = (tuple(meta['dirs']), al)
            costs[kk] = v['hints']
            if v['module'].split('.')[-1] in a.first:
                first.append((a.first.index(v['module'].split('.')[-1]), kk))
    first = [kk for _, kk in sorted(first)]
    A = Automaton(L, k, K)
    U, V, W, WIN = all_candidates(A)
    blockers = [frozenset(x for x in ws if x in keep) for ws in WIN]
    blocked_by = {}
    for i, b in enumerate(blockers):
        for x in b:
            blocked_by.setdefault(x, []).append(i)
    alive = np.array([len(b) for b in blockers])

    def state():
        mask = alive == 0
        lam, pi = mean_and_potential(A, U[mask], V[mask], W[mask])
        if pi is None:
            return lam, None, None
        rng = int(pi.max() - pi.min())
        return lam, rng, lean_bound(lam.numerator, lam.denominator, a.bits) if rng <= (1 << a.bits) - 1 else None

    lam, rng, b = state()
    total = sum(costs[x] for x in keep)
    print(f'start: {len(keep)} exclusions, mean {lam}, range {rng}, Lean bound {b}, proof lines {total}', flush=True)
    assert b is not None and b <= a.target_edges
    order = [x for x in first if x in keep] + [x for x in sorted(keep, key=lambda x: -costs[x]) if x not in first]
    for x in order[:a.tries]:
        es = np.array(blocked_by[x])
        alive[es] -= 1
        lam2, rng2, b2 = state()
        ok = b2 is not None and b2 <= a.target_edges
        print(f'drop {x} ({costs[x]} lines): mean {lam2}, range {rng2}, bound {b2} -> {"DROPPED" if ok else "kept"}',
              flush=True)
        if ok:
            keep.discard(x)
            lam, rng, b = lam2, rng2, b2
        else:
            alive[es] += 1
    total2 = sum(costs[x] for x in keep)
    print(f'end: {len(keep)} exclusions, mean {lam}, range {rng}, Lean bound {b}, proof lines {total2} '
          f'({100 * total2 / total:.0f}% of {total})', flush=True)
    out = {'L': L, 'k': k, 'K': K, 'radius': radius, 'min_mean': str(lam), 'potential_range': rng,
           'lean_bound': b, 'total_proof_lines': total2,
           'exclusions': [{'dirs': list(x[0]), 'alpha': [list(r) for r in x[1]]} for x in sorted(keep)]}
    path = a.out or a.set.replace('.json', '_pruned.json')
    json.dump(out, open(path, 'w'), indent=1)
    print('wrote', path)
    if a.index:
        idx = json.load(open(a.index))
        cases = [c for c in idx['cases'] if (tuple(c['dirs']), tuple(map(tuple, c['alpha']))) in keep]
        assert len(cases) == len(keep), (len(cases), len(keep))
        idx = dict(idx, cases=cases, source_set=os.path.basename(path),
                   note='subset of %s kept by prune_costly.py' % os.path.basename(a.index))
        ipath = path.replace('.json', '_index.json')
        json.dump(idx, open(ipath, 'w'), indent=1)
        print('wrote', ipath, len(cases), 'certificates')


if __name__ == '__main__':
    main()
