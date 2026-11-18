"""Alternative encodings of the corner-share cap of a 7-centre window (track A, milestone 38).

AltShare(window, alpha, radius, M, cap, mode, order, step) keeps wincert.Encoding and the per-corner
clauses of share7.SubShareEncoding (emptyE, the e0 / degree totalizers, shareCl: u[q,t] is forced for
t <= floor(M e0(q) / d(q))) and replaces only the cap counter over the u literals:

  flat    the production counter: one balanced totalizer over all u literals in list order
  merge   balanced merge tree of the per-corner unary numbers (corners grouped by centre), truncated at cap + 1
  seq     the same merges as a left-deep chain (a sequential counter over the corners)
self.cen[c] is the unary output of centre c in mode merge (for per-centre cubes).
order = True adds u[q,t+1] -> u[q,t] (removes the freedom of the auxiliary u literals).
step = s > 1 keeps only u[q,t] with s | t, each worth s (a coarser, weaker count: UNSAT still proves
share >= cap + 1 because sum_q s floor(v_q / s) <= sum_q v_q).
Solver experiments only: none of the variants is a certificate format of the Lean pipeline."""
import itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, os.path.join(MS, '28-combined-identities'))
sys.path.insert(0, os.path.join(MS, '11-local-ceiling', 's0_share_loop'))
import share7, wincert_share as ws


class AltShare(share7.SubShareEncoding):
    def __init__(self, window, alpha, radius, M, cap, mode='flat', order=False, step=1):
        self.mode, self.order, self.step = mode, order, step
        super().__init__(window, alpha, radius, M, cap, range(1, len(window) - 1))

    def merge(self, a, b, lim):
        na, nb = len(a) - 1, len(b) - 1
        no = min(na + nb, lim)
        o = [None] + [self.fresh() for _ in range(no)]
        for i in range(na + 1):
            for j in range(nb + 1):
                if i + j == 0:
                    continue
                k = min(i + j, no)
                if i + j > no and ((i > 0 and i + j - 1 >= no and j > 0)):
                    # a smaller pair already gives the top output
                    if (i - 1) + j >= no or i + (j - 1) >= no:
                        continue
                c = [o[k]]
                if i: c.append(-a[i])
                if j: c.append(-b[j])
                self.add(c, 'totUp')
        return o

    def tree(self, xs, lim):
        if len(xs) == 1:
            return xs[0]
        h = len(xs) // 2
        return self.merge(self.tree(xs[:h], lim), self.tree(xs[h:], lim), lim)

    def build_share(self):
        if self.mode == 'flat' and not self.order and self.step == 1:
            return super().build_share()
        X, B, M, cap, st = self.var, self.B, self.M, self.cap, self.step
        w = self.window
        self.sq, self.tots, self.qs, self.ulits = {}, [], [], []
        lim = cap // st + 1                       # need count >= lim units of st to exceed cap
        per = {}
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ 1 << kk
                Es = []
                for a, b in itertools.combinations(range(9), 2):
                    if kk in (a, b):
                        continue
                    sq = [q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b]
                    e = self.fresh(); Es.append(e); self.sq[(q, a, b)] = e
                    self.add([X[v] for v in sq] + [e], 'emptyE')
                nb = [q ^ 1 << t for t in range(9)]
                ge_e = self.totalizer(Es, up=True)
                ge_d = self.totalizer([X[v] for v in nb], up=False, down=True)
                nE = len(Es)
                us = [None]
                for t in range(st, min(cap + st, M * nE) + 1, st):
                    if len(us) - 1 >= lim:
                        break
                    u = self.fresh(); us.append(u)
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
                if self.order:
                    for t in range(1, len(us) - 1):
                        self.add([-us[t + 1], us[t]], 'uOrder')
                self.ulits += us[1:]
                per.setdefault(ci, []).append(us)
                self.qs.append(dict(c=ci, kk=kk, q=q, u=us[1:]))
        if self.mode == 'flat':
            o = self.totalizer(self.ulits, up=True, limit=lim)
        elif self.mode == 'merge':
            self.cen = {ci: self.tree(v, lim) for ci, v in per.items()}
            o = self.tree([self.cen[ci] for ci in sorted(per)], lim)
        elif self.mode == 'seq':
            xs = [u for ci in sorted(per) for u in per[ci]]
            o = xs[0]
            for x in xs[1:]:
                o = self.merge(o, x, lim)
        else:
            raise ValueError(self.mode)
        self.top = o
        if len(o) - 1 >= lim:
            self.add([-o[lim]], 'shareCap')
