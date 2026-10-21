"""Certificate count and exact potential for the converged k6 automata (dual pruning, as minimize.py).

Variant A (weight sym) or B (weight 120 sym + T5_lb).  With lambda = p/q the minimum mean, an integer
potential pi with q*w - p + pi[u] - pi[v] >= 0 on every kept edge is found by Bellman-Ford.  Every
removed edge gets its blockers (the UNSAT keys among its 6-window, its 5-window and the 5-window's
sub-windows).  An exclusion X is dropped when every edge whose blockers lie in dropped + {X} has
non-negative slack under pi; repeat with a fresh potential until stable.  Only exclusions that act on
edges of the lifted graph are counted: the k5 pickle's own exclusions (radius-4 oracle cache at
build time) are a fixed base, reported separately.  If --target m is given, lambda may be lowered to
the smallest p/q that still gives m <= target through 9171/(mu+35) (then more exclusions drop).
usage: minimal.py A|B [--target M]
"""
import sys, os, json, time, argparse
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
import k6loop as K
from refine import howard


def lean_bound(lam, unit, bits):
    """Plain variant only (unit 1): the gen_lean_chain5 arithmetic, (P + 35 Q) m <= 9171 Q + C with
    C = (2^bits - 1) + 7 P - 6 Q.  For k = 6 the leading-step constant may differ slightly (not derived)."""
    if unit != 1:
        return None
    P, Q = lam.numerator, lam.denominator
    C = (1 << bits) - 1 + 7 * P - 6 * Q
    return (9171 * Q + C) // (P + 35 * Q)


def potential(n, U, V, w):
    pi = np.zeros(n, np.int64)
    for it in range(20000):
        cand = pi[U] + w
        new = pi.copy(); np.minimum.at(new, V, cand)
        if (new == pi).all():
            return pi, it
        pi = new
    return None, it


def main():
    ap = argparse.ArgumentParser(); ap.add_argument('variant'); ap.add_argument('--target', type=int); ap.add_argument('--bits', type=int, default=8); ap.add_argument('--lam')
    a = ap.parse_args()
    G = K.build(); P = K.Plain()
    unit = 1 if a.variant == 'A' else K.UNIT
    if a.variant == 'A':
        T5 = np.zeros(len(G['keys5']), np.int64)
    else:
        rs, O = K.share_oracle()
        T5 = np.array([O.st[k]['lb'] if k in O.st else 0 for k in G['keys5']], np.int64)
    W = unit * G['S'].astype(np.int64) + T5[G['K5']]
    # blockers per key index
    ukeys = {}
    def kid(k):
        return ukeys.setdefault(k, len(ukeys))
    bl5 = []
    for k in G['keys5']:
        b = ([kid(k)] if P.st.get(k) == 'UNSAT' else []) + [kid(s) for s in K.subwindows(k) if P.st.get(s) == 'UNSAT']
        bl5.append(b)
    bl6 = [[kid(k)] if P.st.get(k) == 'UNSAT' else [] for k in G['keys6']]
    inv = {v: k for k, v in ukeys.items()}
    dropped = set()

    def blocked_mask():
        b5 = np.array([any(x not in dropped for x in b) for b in bl5], bool)
        b6 = np.array([any(x not in dropped for x in b) for b in bl6], bool)
        return b5[G['K5']] | b6[G['K6']]

    blk = blocked_mask()
    idx = K.live(G, ~blk)
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], W[idx])
    lam = Fr(int(W[idx][cyc].sum()), len(cyc))
    lam0 = lam
    if a.target:
        # lower lambda to the smallest p/q (q <= 40) whose Lean arithmetic still gives the target:
        # (P + 35 Q unit) m <= 9171 Q unit + C,  C = (2^B - 1) + 7 P - 6 Q unit  (as gen_lean_chain5; B = 7 assumed)
        cands = []
        for q in range(1, 41):
            for p in range(int(lam * q), int(Fr(7, 2) * unit * q), -1):
                f = Fr(p, q)
                C = (1 << a.bits) - 1 + 7 * p - 6 * q
                if unit == 1 and (9171 * q + C) // (p + 35 * q) <= a.target:
                    cands.append(f)
                else:
                    break
        if cands:
            lam = min(cands)
    if a.lam:
        lam = Fr(a.lam)
    p, q = lam.numerator, lam.denominator
    print(f'variant {a.variant}: min mean {lam0} (mu {float(lam0)/unit:.5f}); using lambda {lam} (mu {float(lam)/unit:.5f}, '
          f'm <= {K.bound_m(float(lam)/unit):.3f}); {len(ukeys)} UNSAT keys act on the lifted graph', flush=True)
    E = np.arange(len(G['U']))
    eb5 = [bl5[i] for i in range(len(bl5))]
    for sweep in range(10):
        keep = ~blocked_mask()
        pi, it = potential(G['n6'], G['U'][keep], G['V'][keep], q * W[keep] - p)
        assert pi is not None, 'negative cycle'
        slack = q * W - p + pi[G['U']] - pi[G['V']]
        bad = slack < 0                                      # edges that must stay blocked
        # an edge with negative slack needs at least one of its blockers kept
        must = {}
        badE = np.nonzero(bad & ~keep)[0]
        for e in badE:
            b = [x for x in bl5[G['K5'][e]] + bl6[G['K6'][e]] if x not in dropped]
            must.setdefault(tuple(sorted(set(b))), 0)
        # greedy: try to drop keys, larger windows (6-centre) first, then 5-centre
        keyorder = sorted((x for x in ukeys.values() if x not in dropped), key=lambda x: -len(inv[x][1]))
        crit = [set(b) for b in must]
        n0 = len(dropped)
        for x in keyorder:
            if all(len(c - {x}) > 0 for c in crit if x in c):
                ok = True
                for c in crit:
                    if x in c:
                        c.discard(x)
                dropped.add(x)
        print(f' sweep {sweep}: potential range {int(pi.max()-pi.min())} ({it} BF iterations), '
              f'critical edge classes {len(crit)}, dropped {len(dropped)-n0}, kept {len(ukeys)-len(dropped)}', flush=True)
        if len(dropped) == n0:
            break
    keep = ~blocked_mask()
    idx = K.live(G, keep)
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], W[idx])
    lam2 = Fr(int(W[idx][cyc].sum()), len(cyc))
    pi, _ = potential(G['n6'], G['U'][keep], G['V'][keep], q * W[keep] - p)
    # share charges actually needed: a key's T5 can drop to 0 if every kept edge with it keeps slack >= 0
    nshare = None
    if unit > 1:
        sl = q * W - p + pi[G['U']] - pi[G['V']]
        k5 = G['K5'][keep]; need = np.zeros(len(G['keys5']), bool)
        bad = (sl[keep] - q * T5[k5]) < 0
        need[k5[bad]] = True
        need &= T5 > 0
        nshare = int(need.sum())
        lv = np.zeros(len(G['keys5']), bool); lv[G['K5'][idx]] = True
        print(f' share keys with lb > 0 on live edges: {int(((T5 > 0) & lv).sum())}, needed: {nshare}', flush=True)
    kept = [inv[x] for x in ukeys.values() if x not in dropped]
    by_k = {}
    for k in kept:
        by_k[len(k[1])] = by_k.get(len(k[1]), 0) + 1
    src = {}
    for k in kept:
        s = P.src.get(k, '?'); src[s] = src.get(s, 0) + 1
    states = len(np.unique(np.concatenate([G['U'][idx], G['V'][idx]])))
    bits = max(1, int(pi.max() - pi.min()).bit_length())
    Pq = (p, q)
    out = dict(share_needed=nshare, lean_bound=(9171 * q + (1 << bits) - 1 + 7 * p - 6 * q) // (p + 35 * q) if unit == 1 else None, P=p, Q=q, pot_bits=bits, variant=a.variant, min_mean=str(lam0), lam_used=str(lam), mu_used=float(lam) / unit,
               mean_after=str(lam2), m_le=K.bound_m(float(lam2) / unit), kept=len(kept), kept_by_centres=by_k,
               kept_by_source=src, potential_range=int(pi.max() - pi.min()), live_states=int(states),
               live_edges=int(len(idx)), graph_nodes=G['n6'], graph_edges=int(len(G['U'])))
    print(json.dumps(out), flush=True)
    json.dump(dict(out, keys=[[list(k[0]), [list(x) for x in k[1]]] for k in sorted(kept)]),
              open(os.path.join(K.HERE, f'minimal_{a.variant}{"_t%d" % a.target if a.target else ""}{"_l" + a.lam.replace("/", "_") if a.lam else ""}.json'), 'w'))


if __name__ == '__main__':
    main()
