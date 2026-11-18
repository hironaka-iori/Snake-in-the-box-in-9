"""Combined count+share window floor (track B, direction (a)).

For a window (k centres) the combined weight is  W = sum_centres (2 M alpha + shareN_M),
the per-vertex summand of `core_charge_sum_le`:
    sum_{k<=m} (2M alpha_k + share_k) + 70 M (m+1) <= 18428 M.
CombEncoding(window, radius, M, cap, wA) = wincert.Encoding (counts free) + the share clauses of
wincert_share.ShareEncoding (all centres) + wA copies of every singleton literal (corner absent)
fed with the share unit literals into one totalizer, with cap: UNSAT proves W >= cap + 1.
(wA = 2M reproduces W exactly.)"""
import os, sys, itertools, time, json
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
import wincert_share as ws
from wincert import window_from_dirs


class CombEncoding(ws.ShareEncoding):
    def __init__(self, window, radius, M, cap, wA=None, alpha=None):
        self.wA = 2 * M if wA is None else wA
        k = len(window) - 2
        super().__init__(window, alpha if alpha is not None else [None] * k, radius, M, cap)

    def build_share(self):
        X, B, M, cap = self.var, self.B, self.M, self.cap
        w = self.window
        self.sq, self.tots, self.qs, self.ulits = {}, [], [], []
        alits = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            for a, b in itertools.combinations(range(9), 2):
                if a not in used and b not in used:
                    alits.append(-X[c ^ 1 << a ^ 1 << b])
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ 1 << kk
                Es = []
                for a, b in itertools.combinations(range(9), 2):
                    if kk in (a, b):
                        continue
                    sq = [q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b]
                    e = self.fresh(); Es.append(e)
                    self.add([X[v] for v in sq] + [e], 'emptyE')
                nb = [q ^ 1 << t for t in range(9)]
                ge_e = self.totalizer(Es, up=True)
                ge_d = self.totalizer([X[v] for v in nb], up=False, down=True)
                nE = len(Es)
                tmax = min(cap + 1, M * nE)
                for t in range(1, tmax + 1):
                    u = self.fresh(); self.ulits.append(u)
                    for dd in range(1, 10):
                        cneed = ws.ceil_div(t * dd, M)
                        if cneed > nE:
                            continue
                        cl = [u]
                        if cneed >= 1:
                            cl.append(-ge_e[cneed])
                        if dd <= 8:
                            cl.append(ge_d[dd + 1])
                        self.add(cl, 'shareCl')
        self.alits = alits
        # weighted alpha: wA copies of each alpha literal (same literal, so the totalizer counts it wA times)
        o = self.totalizer(self.ulits + [l for l in alits for _ in range(self.wA)], up=True, limit=cap + 1)
        if len(o) - 1 >= cap + 1:
            self.add([-o[cap + 1]], 'combCap')


def exact(window, sel, M):
    S = set(sel); A = []; SH = []
    for ci in range(1, len(window) - 1):
        c = window[ci]
        used = {(c ^ window[ci - 1]).bit_length() - 1, (c ^ window[ci + 1]).bit_length() - 1}
        A.append(sum(1 for a, b in itertools.combinations(range(9), 2)
                     if a not in used and b not in used and (c ^ 1 << a ^ 1 << b) not in S))
        sh = 0
        for kk in range(9):
            if kk in used: continue
            q = c ^ 1 << kk
            if q in S: continue
            e0 = sum(1 for a, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            sh += (M * e0) // d
        SH.append(sh)
    return A, SH


def test(dirs, T, M=2, radius=4, tl=120):
    """Is 'W_M <= T - 1' satisfiable?  UNSAT: W_M >= T."""
    w = window_from_dirs(list(dirs))
    t0 = time.time()
    enc = CombEncoding(w, radius, M, T - 1)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(dirs), M=M, T=T, result=st, seconds=round(time.time() - t0, 1),
             nv=enc.nv, ncl=len(enc.clauses))
    if sel:
        A, SH = exact(w, sel, M)
        A12, SH12 = exact(w, sel, 12)
        r.update(alpha=A, share=SH, W=sum(2 * M * a for a in A) + sum(SH),
                 W12=sum(24 * a for a in A12) + sum(SH12), share12=SH12)
    return r


if __name__ == '__main__':
    dirs = json.loads(sys.argv[1]); T = int(sys.argv[2]); M = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    print(json.dumps(test(dirs, T, M, tl=float(sys.argv[4]) if len(sys.argv) > 4 else 120)))
