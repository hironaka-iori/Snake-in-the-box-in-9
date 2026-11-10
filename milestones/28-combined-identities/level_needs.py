"""Key / threshold sets behind one bound level (Refinement toward 232).

For lambda_t = P/Q, Bellman-Ford on the allowed transitions (weights Q (120 A + S5) - P) gives the
potential pi of eval232.py.  With pi fixed:
  * a share bound is used on an allowed transition iff Q 120 A - P + pi(u) - pi(v) < 0; the needed
    value is T = ceil((P - Q 120 A - pi(u) + pi(v)) / Q).  It is covered by the Lean floors of main
    (comb.CERT_SHARE), else by a 5-window threshold (RefutedShare, M = 12, key = 5-window), else by a
    context threshold (share7.py, ctx 7 or 8);
  * an exclusion is used on an excluded transition iff Q (120 A + S5) - P + pi(u) - pi(v) < 0 (S5 the
    proved bound of that transition).  One key per such transition: its shortest suffix window that is
    a known UNSAT key (greedy, so the count is an upper bound of a minimal set for this potential).
Counts by key length and source (new = found by this section, data/oracle_plain_r232.jsonl), and the
needed-T histograms, go to data/level_<P>_<Q>.json.
usage: level_needs.py P/Q
"""
import sys, os, json, time, itertools, gzip
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import share7 as S7

SCR = C.SCR


def main():
    lam = Fr(sys.argv[1]); P, Q = lam.numerator, lam.denominator
    G = C.build('all', with_share=True, with_w3=False)
    n = int(G['n'])
    w = C.weights(G, 1, 0)
    U = G['U'].astype(np.int64); V = G['V'].astype(np.int64)
    pi, it = C.bellman_ford(n, U, V, Q * w - P, 40000)
    assert pi is not None, 'lambda_t above the minimum cycle mean'
    R = int(pi.max() - pi.min()); bound = int(C.bound_m(P, Q, R, 1, 0, 0))
    C.log(f'lambda_t {lam}: R {R}, {it} rounds, bound {bound}')
    # ---- shares used on allowed transitions
    A = G['A'].astype(np.int64)
    red0 = Q * 120 * A - P + pi[U] - pi[V]
    used = np.nonzero(red0 < 0)[0]
    need = -(-(-red0[used]) // Q)
    Gc = C.build('cert', with_share=True, with_w3=False, certified_share=True)   # floors of main only
    pc = np.searchsorted(Gc['G'], G['G'][used])
    pc = np.minimum(pc, len(Gc['G']) - 1)
    cert = np.where(Gc['G'][pc] == G['G'][used], Gc['S5'][pc], 0)
    del Gc
    os.environ['NOCTX'] = '1'
    G5 = C.build('all', with_share=True, with_w3=False)                          # 5-window data only
    del os.environ['NOCTX']
    p5 = np.searchsorted(G5['G'], G['G'][used]); p5 = np.minimum(p5, len(G5['G']) - 1)
    s5 = np.where(G5['G'][p5] == G['G'][used], G5['S5'][p5], 0)
    del G5
    keys5, keysx = {}, {}
    nc = 0
    for e, T, cv, fv in zip(used, need, cert, s5):
        T = int(T)
        if cv >= T:
            nc += 1; continue
        ds, t, k5, k6 = C.step_windows(int(G['G'][e]))
        if fv >= T:
            keys5[k5] = max(keys5.get(k5, 0), T)
        else:
            kx = (C.canon(ds[1:8]), t)
            keysx[kx] = max(keysx.get(kx, 0), T)
    # ---- exclusions used on excluded transitions (full product with no key)
    empty = os.path.join(SCR, 'nokeys.json'); json.dump({'keys': []}, open(empty, 'w'))
    Ga = C.build(empty, with_share=True, with_w3=False)
    allowed = np.isin(Ga['G'], G['G'])
    ex = np.nonzero(~allowed)[0]
    wa = 120 * Ga['A'][ex].astype(np.int64) + Ga['S5'][ex]
    red = Q * wa - P + pi[Ga['U'][ex].astype(np.int64)] - pi[Ga['V'][ex].astype(np.int64)]
    bad = ex[red < 0]
    C.log(f'shares used on {len(used)} transitions ({nc} by main floors); exclusions used on {len(bad)} transitions')
    # k6loop.OPLAIN is a module global that the first fp.Status() redirects; restore it so this second
    # Status also reads 11-local-ceiling/k6_loop/oracle_plain.jsonl
    C.fp.K6.OPLAIN = os.path.join(C.MS, '11-local-ceiling', 'k6_loop', 'oracle_plain.jsonl')
    S = C.fp.Status()
    new = set()
    f = os.path.join(HERE, 'data', 'oracle_plain_r232.jsonl')
    for l in (open(f) if os.path.exists(f) else []):
        r = json.loads(l)
        if r['result'] == 'UNSAT':
            for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                new.add(C.fp.lkey(tuple(r['dirs']), t))
    for k in C.own_plain_unsat():
        S.st.setdefault(k, 'UNSAT')
        if S.st[k] != 'UNSAT':
            S.st[k] = 'UNSAT'
    Pr = C.fp.Product()
    chosen = {}
    miss = 0
    for g in Ga['G'][bad]:
        for k in Pr.windows(int(g)):
            if S.st.get(k) == 'UNSAT' or k in new:
                chosen[k] = chosen.get(k, 0) + 1
                break
        else:
            miss += 1
    byk = {}
    for k in chosen:
        tag = f"{len(k[1]) + 1}dir_{'new' if k in new else 'old'}"
        byk[tag] = byk.get(tag, 0) + 1

    def hist(d):
        h = {}
        for T in d.values():
            b = 16 if T <= 16 else 24 if T <= 24 else 48 if T <= 48 else 72 if T <= 72 else 108 if T <= 108 else 999
            h[b] = h.get(b, 0) + 1
        return {str(k): v for k, v in sorted(h.items())}
    out = dict(lam_t=str(lam), R=R, bound=bound, bf_rounds=it,
               share_transitions=int(len(used)), covered_by_main_floors=nc,
               share5_keys=len(keys5), share5_T_hist=hist(keys5),
               ctx_keys=len(keysx), ctx_T_hist=hist(keysx),
               excluded_transitions_used=int(len(bad)), plain_keys=len(chosen), plain_keys_by=byk,
               unmatched=miss)
    C.log(json.dumps(out))
    out['ctx_rows'] = [[list(k[0]), list(k[1]), T] for k, T in sorted(keysx.items())]
    json.dump(out, open(os.path.join(HERE, 'data', f'level_{P}_{Q}.json'), 'w'))


if __name__ == '__main__':
    main()
