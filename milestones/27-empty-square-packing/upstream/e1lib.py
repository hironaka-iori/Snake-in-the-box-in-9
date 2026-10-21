"""E1: minimum s0 corner share (dom rule) at window centres, radius-r local snake model.

Model: wincert.Encoding (milestones/10-window-aggregate/scripts/wincert.py), unchanged, plus
  E[q,ij]  <- square {q,q^i,q^j,q^ij} has no selected vertex       (only the forcing direction)
  ge_e[q][c] <- at least c of the E[q,*] are true                   (totalizer, upward)
  ge_d[q][t] -> at least t neighbours of q are selected             (totalizer on selected nbrs, downward)
  u[q,t] <- ge_e[q][c] & ~ge_d[q][dd+1]   for every dd, c = ceil(t*dd/M)
so in every real configuration  sum_t u[q,t] >= floor(M*e0(q)/d(q))  is forced, and a bound
sum u <= K that is UNSAT proves shareN >= K+1 for every configuration of the model.
The model value reported for SAT witnesses is recomputed exactly from the selection.
Lazy cycle cuts as in wincert.decide (a cycle of selected vertices is not a snake piece).
"""
import itertools, os, sys, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../10-window-aggregate/scripts'))
import wincert
from pysat.card import ITotalizer
from pysat.solvers import Cadical153


def unary_ge(enc, lits, up=True, down=False):
    """Totalizer returning o[1..n] with o[c] <-> (#true >= c) in requested directions."""
    def rec(ls):
        if len(ls) == 1:
            return [None, ls[0]]
        a = rec(ls[:len(ls) // 2]); b = rec(ls[len(ls) // 2:])
        na, nb = len(a) - 1, len(b) - 1
        o = [None] + [enc.fresh() for _ in range(na + nb)]
        for i in range(na + 1):
            for j in range(nb + 1):
                if up and i + j > 0:   # a>=i & b>=j -> o>=i+j
                    c = [o[i + j]]
                    if i: c.append(-a[i])
                    if j: c.append(-b[j])
                    enc.add(c, 'tot_up')
                if down and i + j + 1 <= na + nb:  # a<i+1 & b<j+1 -> o<i+j+1
                    c = [-o[i + j + 1]]
                    if i + 1 <= na: c.append(a[i + 1])
                    if j + 1 <= nb: c.append(b[j + 1])
                    enc.add(c, 'tot_down')
        return o
    return rec(list(lits))


def ceil_div(a, b):
    return -(-a // b)


class ShareModel:
    def __init__(self, dirs, alphas, radius, M, share_centres=None, tcap=60):
        self.win = wincert.window_from_dirs(dirs)
        self.dirs, self.alphas, self.radius, self.M = dirs, alphas, radius, M
        self.enc = enc = wincert.Encoding(self.win, alphas, radius)
        X, B = enc.var, enc.B
        k = len(self.win) - 2
        self.share_centres = list(range(1, k + 1)) if share_centres is None else share_centres
        self.qinfo = []   # (centre index, q, squares, nbrs)
        self.ulits = []
        for ci in self.share_centres:
            c = self.win[ci]
            used = {(c ^ self.win[ci - 1]).bit_length() - 1, (c ^ self.win[ci + 1]).bit_length() - 1}
            for kk in range(9):
                if kk in used:
                    continue
                q = c ^ 1 << kk
                sqs = []
                for i, j in itertools.combinations(range(9), 2):
                    if kk in (i, j):
                        continue
                    sq = [q, q ^ 1 << i, q ^ 1 << j, q ^ 1 << i ^ 1 << j]
                    assert all(w in B for w in sq)
                    sqs.append(sq)
                nb = [q ^ 1 << t for t in range(9)]
                assert all(w in B for w in nb)
                self.qinfo.append((ci, q, sqs, nb))
                Es = []
                for sq in sqs:
                    e = enc.fresh(); Es.append(e)
                    enc.add([X[w] for w in sq] + [e], 'empty->E')
                ge_e = unary_ge(enc, Es, up=True)
                ge_d = unary_ge(enc, [X[w] for w in nb], up=False, down=True)
                nE = len(Es)
                tmax = min(tcap, M * nE)
                for t in range(1, tmax + 1):
                    u = enc.fresh(); self.ulits.append(u)
                    for dd in range(1, 10):
                        cneed = ceil_div(t * dd, M)
                        if cneed > nE:
                            continue
                        cl = [u]
                        if cneed >= 1:
                            cl.append(-ge_e[cneed])
                        if dd + 1 <= 9:
                            cl.append(ge_d[dd + 1])
                        enc.add(cl, 'share')

    def share_of(self, sel):
        """Exact shareN (per centre) and exact rational dom share for a selection."""
        S = set(sel)
        per = {}
        rat = {}
        for ci, q, sqs, nb in self.qinfo:
            if q in S:
                continue
            e0 = sum(1 for sq in sqs if not any(w in S for w in sq))
            d = sum(1 for w in nb if w in S)
            per[ci] = per.get(ci, 0) + (self.M * e0) // d
            rat[ci] = rat.get(ci, Fr(0)) + Fr(e0, 2 * d)
        return per, rat

    def alpha_of(self, sel, ci):
        S = set(sel); c = self.win[ci]
        used = {(c ^ self.win[ci - 1]).bit_length() - 1, (c ^ self.win[ci + 1]).bit_length() - 1}
        return sum(1 for a, b in itertools.combinations(range(9), 2)
                   if a not in used and b not in used and (c ^ 1 << a ^ 1 << b) not in S)

    def minimise(self, Kmax=60, time_limit=600, log=None):
        """Binary search for the smallest K with a cycle-free model of sum(u) <= K.
        lo = proved lower bound on shareN (all K < lo UNSAT); hi = best witness value."""
        enc = self.enc
        t0 = time.time()
        tot = ITotalizer(lits=self.ulits, ubound=Kmax + 1, top_id=enc.nv)
        cuts = 0
        lo, hi = 0, None
        best = None
        status = 'OPT'
        with Cadical153(bootstrap_with=enc.clauses + tot.cnf.clauses) as s:
            def solve_le(K):
                nonlocal cuts
                while True:
                    ok = s.solve(assumptions=[-tot.rhs[K]] if K <= Kmax else [])
                    if not ok:
                        return None
                    m = s.get_model()
                    sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
                    cyc = wincert.cycles_of(sel)
                    if not cyc:
                        return sel
                    for cc in cyc:
                        s.add_clause([-enc.var[w] for w in cc]); cuts += 1
            sel = solve_le(Kmax + 1)
            if sel is None:
                return {'status': 'UNSAT_MODEL', 'cuts': cuts}
            per, rat = self.share_of(sel)
            hi = sum(per.values()); best = (sel, per, rat)
            if log: log(f'   initial witness shareN={hi} [{time.time()-t0:.1f}s]')
            if hi > Kmax:
                hi = Kmax + 1
            while lo < hi:
                if time.time() - t0 > time_limit:
                    status = 'TIMEOUT'; break
                mid = (lo + hi) // 2 if hi - lo > 4 else hi - 1
                sel = solve_le(mid)
                if sel is None:
                    lo = mid + 1
                    if log: log(f'   K<={mid}: UNSAT  [{time.time()-t0:.1f}s cuts {cuts}]')
                else:
                    per, rat = self.share_of(sel)
                    val = sum(per.values()); assert val <= mid
                    hi = val; best = (sel, per, rat)
                    if log: log(f'   K<={mid}: SAT witness {val} [{time.time()-t0:.1f}s]')
        sel, per, rat = best
        return {'status': status, 'min_lower': lo, 'witness_share': hi, 'per': per,
                'rat': {k: str(v) for k, v in rat.items()},
                'alphas': [self.alpha_of(sel, ci) for ci in range(1, len(self.win) - 1)],
                'sel': sel, 'cuts': cuts, 'seconds': round(time.time() - t0, 1),
                'nvars': enc.nv, 'nclauses': len(enc.clauses) + len(tot.cnf.clauses)}


def minimise2(self, Kmax=60, time_limit=500, budget=300000, log=None):
    """Descend from witnesses (conflict-budgeted SAT calls), then prove lower bounds ascending.
    Returns proved lower bound lo (all K<lo UNSAT) and best witness hi (exact share of a model)."""
    enc = self.enc
    t0 = time.time()
    tot = ITotalizer(lits=self.ulits, ubound=Kmax + 1, top_id=enc.nv)
    cuts = 0
    with Cadical153(bootstrap_with=enc.clauses + tot.cnf.clauses) as s:
        def solve_le(K, limited):
            nonlocal cuts
            while True:
                if time.time() - t0 > time_limit:
                    return 'TIME'
                ass = [-tot.rhs[K]] if K <= Kmax else []
                if limited:
                    s.conf_budget(budget); ok = s.solve_limited(assumptions=ass)
                    if ok is None:
                        return 'UNKNOWN'
                else:
                    s.conf_budget(-1); ok = s.solve_limited(assumptions=ass)
                    if ok is None:
                        return 'UNKNOWN'
                if not ok:
                    return 'UNSAT'
                m = s.get_model()
                sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
                cyc = wincert.cycles_of(sel)
                if not cyc:
                    return sel
                for cc in cyc:
                    s.add_clause([-enc.var[w] for w in cc]); cuts += 1
        sel = solve_le(Kmax + 1, False)
        if sel == 'UNSAT':
            return {'status': 'UNSAT_MODEL'}
        per, rat = self.share_of(sel); hi = sum(per.values()); best = (sel, per, rat); lo = 0
        if log: log(f'   witness {hi} [{time.time()-t0:.1f}s]')
        # phase 1: descend with budget
        while lo < hi:
            Kq = min(hi - 1, Kmax)
            r = solve_le(Kq, True)
            if isinstance(r, list):
                per, rat = self.share_of(r); hi = sum(per.values()); best = (r, per, rat)
                if log: log(f'   witness {hi} [{time.time()-t0:.1f}s]')
            elif r == 'UNSAT':
                lo = Kq + 1
                if lo < hi:
                    status0 = 'ABOVE_KMAX'; break
                if log: log(f'   K<={hi-1}: UNSAT [{time.time()-t0:.1f}s]')
            else:
                break
        # phase 2: prove lower bounds; try K = hi-1 first, back off to smaller K on per-call time cap
        status = 'OPT'
        top = min(hi - 1, Kmax)
        first = True
        while lo <= top:
            K = top if first else (lo + top) // 2
            first = False
            rem = time_limit - (time.time() - t0)
            if rem <= 5:
                status = 'TIMEOUT'; break
            cap = time.time() + max(20.0, rem / 3)
            r = solve_le(K, True)
            while r == 'UNKNOWN' and time.time() < cap:
                r = solve_le(K, True)
            if isinstance(r, list):
                per, rat = self.share_of(r); hi = sum(per.values()); best = (r, per, rat)
                top = min(hi - 1, Kmax)
                if log: log(f'   witness {hi} [{time.time()-t0:.1f}s]')
            elif r == 'UNSAT':
                lo = K + 1
                if log: log(f'   K<={K}: UNSAT [{time.time()-t0:.1f}s cuts {cuts}]')
            else:
                top = K - 1
                if log: log(f'   K<={K}: unknown, backing off [{time.time()-t0:.1f}s]')
        if lo < hi and status == 'OPT':
            status = 'TIMEOUT'
    sel, per, rat = best
    return {'status': status, 'min_lower': lo, 'witness_share': hi, 'per': per,
            'rat': {k: str(v) for k, v in rat.items()}, 'rat_total': str(sum(rat.values())),
            'alphas': [self.alpha_of(sel, ci) for ci in range(1, len(self.win) - 1)],
            'sel': sel, 'cuts': cuts, 'seconds': round(time.time() - t0, 1)}


ShareModel.minimise2 = minimise2
