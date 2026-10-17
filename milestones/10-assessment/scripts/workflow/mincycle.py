"""Exact minimum-mean cycle over bi-infinite alpha sequences whose every length-k window is allowed.
Karp's algorithm on the order-(k-1) de Bruijn graph, values 1..K (K means '>=K', conservative)."""
import numpy as np, itertools
from fractions import Fraction

BASE2 = {(1, 1), (1, 2), (2, 1), (1, 3), (3, 1)}

def allowed_mask(k, K, forb):
    """forb: set of forbidden tuples of length 2..k (already closed under reversal)."""
    shape = (K,) * k
    ok = np.ones(shape, dtype=bool)
    for idx in itertools.product(range(K), repeat=k):
        t = tuple(i + 1 for i in idx)
        bad = False
        for L in range(2, k + 1):
            for s in range(0, k - L + 1):
                if t[s:s + L] in forb:
                    bad = True; break
            if bad:
                break
        if bad:
            ok[idx] = False
    return ok

def min_mean_cycle(k, K, forb):
    ok = allowed_mask(k, K, forb)
    INF = 10 ** 8
    pen = np.where(ok, 0, INF).astype(np.int64)
    vals = np.arange(1, K + 1, dtype=np.int64)
    n = K ** (k - 1)
    D = np.empty((n + 1,) + (K,) * (k - 1), dtype=np.int64)
    P = np.empty((n + 1,) + (K,) * (k - 1), dtype=np.int16)
    D[0] = 0
    for step in range(1, n + 1):
        cand = D[step - 1][..., None] + pen  # axes: a, b.., e
        arg = cand.argmin(axis=0)
        best = np.take_along_axis(cand, arg[None], axis=0)[0]
        best = best + vals.reshape((1,) * (k - 2) + (K,))
        best = np.minimum(best, INF)
        D[step] = best
        P[step] = arg
    Dn = D[n].reshape(-1)
    Df = D.reshape(n + 1, -1)
    lam_best = None; v_best = None
    valid = Df[:n] < INF
    num = (Dn[None, :] - Df[:n]).astype(np.float64)
    den = (n - np.arange(n)).astype(np.float64)[:, None]
    ratio = np.where(valid, num / den, -np.inf)
    worstf = ratio.max(axis=0)
    worstf = np.where(Dn < INF, worstf, np.inf)
    vmin = float(worstf.min())
    for v in np.nonzero(worstf <= vmin + 1e-9)[0][:50]:
        v = int(v)
        sarg = np.nonzero(ratio[:, v] >= worstf[v] - 1e-9)[0]
        worst = max(Fraction(int(Dn[v] - Df[s, v]), n - int(s)) for s in sarg)
        if lam_best is None or worst < lam_best:
            lam_best, v_best = worst, v
    # trace walk of length n ending at v_best
    node = np.unravel_index(v_best, (K,) * (k - 1))
    walk = [tuple(int(i) for i in node)]
    for step in range(n, 0, -1):
        a = int(P[step][node])
        node = (a,) + tuple(int(i) for i in node[:-1])
        walk.append(node)
    walk.reverse()
    # extract cycles
    best_cyc = None
    pos = {}
    stack = []
    for nd in walk:
        if nd in pos:
            i = pos[nd]
            cyc = stack[i:]
            seq = [c[-1] + 1 for c in cyc]
            mean = Fraction(sum(seq), len(seq))
            if best_cyc is None or mean < best_cyc[0]:
                best_cyc = (mean, seq)
            for c in cyc:
                del pos[c]
            stack = stack[:i]
        pos[nd] = len(stack); stack.append(nd)
    return lam_best, best_cyc

def sym(ps):
    return set(ps) | {tuple(reversed(p)) for p in ps}

if __name__ == '__main__':
    import json, time
    r3 = json.load(open('/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/ana/patterns_r3_s9.json'))
    st = {}
    for r in r3:
        st.setdefault(tuple(r['alpha']), {})[r['shape']] = r['status']
    excl = {p for p, s in st.items() if all(x == 'INFEASIBLE' for x in s.values())}
    for name, F3 in [('proved', {(2, 2, 2)}), ('+223', {(2, 2, 2), (2, 2, 3)}), ('all12', excl)]:
        for k, K in [(3, 12), (4, 9), (5, 8)]:
            t = time.time()
            lam, cyc = min_mean_cycle(k, K, sym(BASE2) | sym(F3))
            print(name, 'k=%d K=%d' % (k, K), 'min mean', lam, float(lam), 'cycle', cyc, '%.1fs' % (time.time() - t))
