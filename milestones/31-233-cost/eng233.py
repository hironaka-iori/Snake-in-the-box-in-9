"""Cost-aware certificate selection for the share-weighted k6 chain to 233 (milestone 31).

The product is milestone 28's (= the Lean k6 full product, fp.Product: 132 step windows x 6^6 counts,
6,158,592 transitions on 264,384 states).  Transition g = e*NT + x has the new count s and the
trailing 5-window key k5(g) = lkey(ds[2:8], t1..t5).  A certificate set is

  * a set K of plain keys (lumped k6 keys, 2..6 counts): g is allowed iff no key of K excludes it;
  * a share level L(k5) for every 5-window key (0, or a level <= a proved threshold); levels up to the
    Lean floors of origin/main (F(k5): share >= 16 on 012032/012031/012304/012314, 17 on the
    milestone-155 counts) are free.

Step weight Q (120 s + L(k5(g))) - P on the allowed transitions.  Target: Bellman-Ford from 0
converges with range <= 2^B - 1, B from lib233.best_pq; then (*) of milestone 28 gives m <= 233.

Methods (World):
  bf()            full Bellman-Ford (Jacobi, by target), early exit below -Rmax
  relax(es)       warm incremental relaxation from changed edges (frontier by source), with undo
  dual()          one pass of dual reverse-delete with the potential fixed: every transition with
                  Q 120 s - P + pi(u) - pi(v) < 0 must be excluded by a key of K or have L(k5) >= the
                  needed level; resources visited by decreasing cost (plain keys dropped, share
                  levels lowered to what their uncovered transitions need)
  exact_plain()   exact drops: remove a key, relax warm, keep the removal if the range holds
  exact_share()   exact share lowering: the least level (binary search) that keeps the range
Every result is re-checked by a fresh full Bellman-Ford before it is saved.
"""
import sys, os, json, time, gzip, itertools
import lib233 as L
np = L.np
fp, NT, NC = L.fp, L.NT, L.NC
OVH_CERT = 2.0e4          # objective: hints + this per paid certificate (about 50 KB of Cnf module at 2.5 B/hint)


class World:
    def __init__(self, P, Q, B, pool=None, share=None, verbose=True):
        t0 = time.time()
        self.P, self.Q, self.B = P, Q, B
        self.Rmax = 2 ** B - 1
        Pr = fp.Product(); self.Pr = Pr
        self.N = Pr.nE * NT; self.n = Pr.n
        g = np.arange(self.N, dtype=np.int64)
        u, v, s = Pr.uvw(g)
        self.u = u.astype(np.int32); self.v = v.astype(np.int32); self.s = s.astype(np.int64)
        del u, v, s, g
        # 5-window share keys
        kid = {}; self.k5keys = []
        k5 = np.empty(self.N, np.int32)
        cache = {}
        T5 = list(itertools.product(range(1, 7), repeat=5))
        for e, (i, d, j, ds) in enumerate(Pr.ext):
            c = tuple(ds[2:8])
            if c not in cache:
                arr = np.empty(7776, np.int32)
                for x5, t in enumerate(T5):
                    lk = fp.lkey(c, t)
                    if lk not in kid:
                        kid[lk] = len(self.k5keys); self.k5keys.append(lk)
                    arr[x5] = kid[lk]
                cache[c] = arr
            k5[e * NT:(e + 1) * NT] = np.tile(cache[c], 6)
        self.k5 = k5; self.k5id = kid; self.nS = len(self.k5keys)
        o = np.argsort(k5, kind='stable').astype(np.int32)
        self.sord = o; self.sstart = np.searchsorted(k5[o], np.arange(self.nS + 1)).astype(np.int64)
        o = np.argsort(self.u, kind='stable').astype(np.int32)
        self.uord = o; self.ustart = np.searchsorted(self.u[o], np.arange(self.n + 1)).astype(np.int64)
        del o
        if verbose:
            L.log(f'product: {self.N} transitions, {self.n} states, {self.nS} 5-window keys; '
                  f'{time.time() - t0:.0f}s rss {L.C.rss_mb():.0f}')
        self.load_pool(pool)
        self.load_share(share)
        self.pi = np.zeros(self.n, np.int64)
        if verbose:
            L.log(f'pool {self.nK} plain keys ({len(self.kg)} hits), share ids with data '
                  f'{int((self.slb > 0).sum())}; rss {L.C.rss_mb():.0f}')

    # -------------------------------------------------------------- pool
    def load_pool(self, pool):
        keys = pool if pool is not None else L.plain_pool()
        PC = L.PlainCosts()
        self.keys = keys; self.nK = len(keys)
        self.kid = {k: i for i, k in enumerate(keys)}
        rows = [PC(k) for k in keys]
        self.khints = np.array([r[0] for r in rows]); self.kcore = np.array([r[1] for r in rows])
        self.kbasis = [r[2] for r in rows]
        self.kfree = np.array([b == 'reuse' for b in self.kbasis])
        self.kcost = np.where(self.kfree, 0.0, self.khints + OVH_CERT)
        segs = [self.Pr.edges_of(k).astype(np.int32) for k in keys]
        self.kptr = np.zeros(self.nK + 1, np.int64)
        self.kptr[1:] = np.cumsum([len(x) for x in segs])
        self.kg = np.concatenate(segs)
        del segs
        self.chosen = np.ones(self.nK, bool)
        self.recount()

    def hits(self, j):
        return self.kg[self.kptr[j]:self.kptr[j + 1]]

    def recount(self):
        m = np.repeat(self.chosen, np.diff(self.kptr))
        self.cnt = np.bincount(self.kg[m], minlength=self.N).astype(np.int32)

    def set_chosen(self, chosen):
        self.chosen = np.array(chosen, bool); self.recount()

    # -------------------------------------------------------------- share
    def load_share(self, share):
        lb, calls = share if share is not None else L.share_lb()
        F = L.share_floor()
        self.slb = np.zeros(self.nS, np.int64); self.sF = np.zeros(self.nS, np.int64)
        self.scalls = [[] for _ in range(self.nS)]
        for k, v in lb.items():
            i = self.k5id.get(k)
            if i is not None:
                self.slb[i] = max(self.slb[i], v)
        for k, v in F.items():
            i = self.k5id.get(k)
            if i is not None:
                self.sF[i] = max(self.sF[i], v)
        for k, cs in calls.items():
            i = self.k5id.get(k)
            if i is not None:
                self.scalls[i] = sorted(cs)
        self.slb = np.maximum(self.slb, self.sF)
        self.smeas = {}                      # (id) -> [(T, hints)] measured replays
        if os.path.exists(L.REPLAY233):
            for l in open(L.REPLAY233):
                r = json.loads(l)
                if r.get('kind') == 'share' and r.get('hints') is not None:
                    i = self.k5id.get(L.lk_of(r['dirs'], r['syms']))
                    if i is not None:
                        self.smeas.setdefault(i, []).append((int(r['T']), float(r['hints'])))
                if r.get('kind') == 'share' and r.get('result') == 'UNSAT':
                    i = self.k5id.get(L.lk_of(r['dirs'], r['syms']))
                    if i is not None:
                        self.scalls[i] = sorted(self.scalls[i] + [(int(r['T']), float(r['solve_s']))])
        self.cal = L.calib()['share']
        self.lvl = self.slb.copy()

    def share_cost(self, i, lv):
        """(hints, basis) of a share certificate at level lv for 5-key id i."""
        if lv <= self.sF[i]:
            return 0.0, 'lean_floor'
        ms = [h for T, h in self.smeas.get(i, ()) if T >= lv]
        cs = [s for T, s in self.scalls[i] if T >= lv and s is not None]
        h = None
        if cs:
            h = L.share_hints(min(cs), self.cal); b = 'model'
        if ms and (h is None or min(ms) < h):
            h = min(ms); b = 'measured'
        if h is None:
            return L.share_hints(1.0, self.cal), 'noseconds'
        return h, b

    def share_obj(self, i, lv):
        h, b = self.share_cost(i, lv)
        return 0.0 if b == 'lean_floor' else h + OVH_CERT

    # -------------------------------------------------------------- weights / BF
    def w(self, es):
        return self.Q * (120 * self.s[es] + self.lvl[self.k5[es]]) - self.P

    def bf(self, maxit=5000, start=None):
        a = np.flatnonzero(self.cnt == 0)
        o = a[np.argsort(self.v[a], kind='stable')]
        U = self.u[o]; V = self.v[o]; W = self.w(o)
        del a
        uv, starts = np.unique(V, return_index=True)
        pi = np.zeros(self.n, np.int64) if start is None else start.copy()
        for it in range(maxit):
            cand = pi[U] + W
            mins = np.minimum.reduceat(cand, starts)
            upd = mins < pi[uv]
            if not upd.any():
                self.pi = pi
                return True, it
            pi[uv[upd]] = mins[upd]
            if pi.min() < -self.Rmax:
                self.pi = pi
                return False, it
        self.pi = pi
        return False, maxit

    def out_edges(self, nodes):
        st = self.ustart[nodes]; ln = self.ustart[nodes + 1] - st
        tot = int(ln.sum())
        if tot == 0:
            return np.zeros(0, np.int64)
        off = np.repeat(st - np.concatenate(([0], np.cumsum(ln)[:-1])), ln)
        return self.uord[off + np.arange(tot)].astype(np.int64)

    def relax(self, es, maxrounds=40):
        """Warm relaxation after the edges es became allowed or cheaper.  True if the potential
        stays within the range (pi updated, a fixed point again); False (pi restored) otherwise."""
        pi = self.pi
        logn, logv = [], []
        es = es[self.cnt[es] == 0]
        for r in range(maxrounds):
            if len(es) == 0:
                return True
            cand = pi[self.u[es]] + self.w(es)
            vv = self.v[es]
            m = cand < pi[vv]
            if not m.any():
                return True
            vv = vv[m]; cand = cand[m]
            nodes = np.unique(vv)
            logn.append(nodes); logv.append(pi[nodes].copy())
            np.minimum.at(pi, vv, cand)
            if pi[nodes].min() < -self.Rmax:
                break
            es = self.out_edges(nodes)
            es = es[self.cnt[es] == 0]
        for nd, ov in zip(reversed(logn), reversed(logv)):
            pi[nd] = ov
        return False

    def check(self):
        ok, it = self.bf()
        return ok and int(-self.pi.min()) <= self.Rmax, it, int(-self.pi.min())

    # -------------------------------------------------------------- dual reverse-delete
    def dual(self):
        Q, P = self.Q, self.P
        pi = self.pi
        red0 = Q * 120 * self.s - P + pi[self.u] - pi[self.v]
        crit = red0 < 0
        need = np.where(crit, (-red0 + Q - 1) // Q, 0)
        del red0
        shcov = crit & (self.lvl[self.k5] >= need)
        items = []
        for j in np.flatnonzero(self.chosen & ~self.kfree):
            items.append((self.kcost[j], 0, int(j)))
        for i in np.flatnonzero(self.lvl > self.sF):
            items.append((self.share_obj(i, self.lvl[i]), 1, int(i)))
        items.sort(key=lambda t: -t[0])
        dk = ds = 0
        for c, kind, j in items:
            if kind == 0:
                gs = self.hits(j)
                gc = gs[crit[gs]]
                if len(gc) and not np.all((self.cnt[gc] >= 2) | shcov[gc]):
                    continue
                self.cnt[gs] -= 1; self.chosen[j] = False; dk += 1
            else:
                es = self.sord[self.sstart[j]:self.sstart[j + 1]]
                ec = es[crit[es]]
                unc = ec[self.cnt[ec] == 0]
                nl = max(int(need[unc].max()) if len(unc) else 0, int(self.sF[j]))
                if nl < self.lvl[j]:
                    self.lvl[j] = nl; ds += 1
                    shcov[ec] = need[ec] <= nl
        return dk, ds, int(crit.sum())

    # -------------------------------------------------------------- exact steps
    def exact_plain(self, order, tlimit=None, log_every=500):
        t0 = time.time(); tried = dropped = 0; saved = 0.0
        for j in order:
            if tlimit and time.time() - t0 > tlimit:
                break
            if not self.chosen[j] or self.kfree[j]:
                continue
            gs = self.hits(j)
            alone = gs[self.cnt[gs] == 1]
            self.cnt[gs] -= 1
            tried += 1
            if self.relax(alone.astype(np.int64)):
                self.chosen[j] = False; dropped += 1; saved += self.kcost[j]
            else:
                self.cnt[gs] += 1
            if tried % log_every == 0:
                L.log(f'  exact plain: {tried} tried, {dropped} dropped, {saved / 1e9:.3f} G saved, range {-self.pi.min()}')
        return tried, dropped, saved

    def share_edges(self, i):
        es = self.sord[self.sstart[i]:self.sstart[i + 1]].astype(np.int64)
        return es[self.cnt[es] == 0]

    def try_level(self, i, nl):
        old = self.lvl[i]
        self.lvl[i] = nl
        if self.relax(self.share_edges(i)):
            return True
        self.lvl[i] = old
        return False

    def exact_share(self, order, tlimit=None):
        t0 = time.time(); tried = lowered = 0; saved = 0.0
        for i in order:
            if tlimit and time.time() - t0 > tlimit:
                break
            cur = int(self.lvl[i]); lo = int(self.sF[i])
            if cur <= lo:
                continue
            tried += 1
            c0 = self.share_obj(i, cur)
            if self.try_level(i, lo):
                lowered += 1; saved += c0; continue
            # least feasible level in (lo, cur]: binary search on [lo+1, cur]
            a, b = lo + 1, cur
            while a < b:
                mid = (a + b) // 2
                if self.try_level(i, mid):
                    b = mid
                else:
                    a = mid + 1
            if a < cur:
                self.try_level(i, a)
                lowered += 1; saved += c0 - self.share_obj(i, a)
        return tried, lowered, saved

    # -------------------------------------------------------------- summary / io
    def summary(self):
        paid = np.flatnonzero(self.chosen & ~self.kfree)
        by = {}
        for j in paid:
            b = self.kbasis[j].split('_')[0]
            a = by.setdefault(b, [0, 0.0]); a[0] += 1; a[1] += self.khints[j]
        sp = [(i, *self.share_cost(i, self.lvl[i])) for i in np.flatnonzero(self.lvl > 0)]
        sh_paid = [(i, h, b) for i, h, b in sp if b != 'lean_floor']
        sby = {}
        for i, h, b in sh_paid:
            a = sby.setdefault(b, [0, 0.0]); a[0] += 1; a[1] += h
        ph = float(self.khints[paid].sum()); sh = float(sum(h for _, h, _ in sh_paid))
        ncent = {}
        for j in paid:
            c = 'H8' if len(self.keys[j]) == 3 else len(self.keys[j][1])
            ncent[c] = ncent.get(c, 0) + 1
        return dict(P=self.P, Q=self.Q, B=self.B, lam=self.P / self.Q, lam_alpha=self.P / self.Q / 120,
                    Rmax=self.Rmax, range=int(-self.pi.min()), bound=L.bound233(self.P, self.Q, self.B),
                    plain_keys=int(self.chosen.sum()), plain_free=int((self.chosen & self.kfree).sum()),
                    plain_paid=len(paid), plain_hints=round(ph), plain_by_basis={k: [v[0], round(v[1])] for k, v in by.items()},
                    plain_paid_by_centres=ncent,
                    share_used=len(sp), share_lean_floor=len(sp) - len(sh_paid), share_paid=len(sh_paid),
                    share_hints=round(sh), share_by_basis={k: [v[0], round(v[1])] for k, v in sby.items()},
                    hints=round(ph + sh), objective=round(ph + sh + OVH_CERT * (len(paid) + len(sh_paid))))

    def save(self, tag, extra=None):
        s = self.summary()
        if extra:
            s.update(extra)
        keys = [[list(self.keys[j][0]), list(self.keys[j][1]), self.kbasis[j], round(float(self.khints[j]))]
                for j in np.flatnonzero(self.chosen) if len(self.keys[j]) == 2]
        h8 = [[list(self.keys[j][1]), list(self.keys[j][2]), round(float(self.khints[j]))]
              for j in np.flatnonzero(self.chosen) if len(self.keys[j]) == 3]
        sh = []
        for i in np.flatnonzero(self.lvl > 0):
            h, b = self.share_cost(i, self.lvl[i])
            k = self.k5keys[i]
            sh.append([list(k[0]), list(k[1]), int(self.lvl[i]), int(self.slb[i]), b, round(h)])
        with gzip.open(os.path.join(L.D, f'set_{tag}.json.gz'), 'wt') as f:
            json.dump(dict(summary=s, plain=keys, share=sh, h8=h8,
                           format=dict(plain='[dirs, lumped syms (1..5, 6 = 6..21), basis, hints]',
                                       share='[dirs, lumped syms, level used T (share sum >= T), proved lb, basis, hints]',
                                       h8='[dirs (8, reversed: uncounted vertex last), 6 lumped syms (reversed), hints]: '
                                          'Refuted (winOf dirs) (boundsOf syms) with the 7th centre uncounted')), f)
        json.dump(s, open(os.path.join(L.D, f'sum_{tag}.json'), 'w'), indent=1)
        return s

    def load(self, tag):
        d = json.load(gzip.open(os.path.join(L.D, f'set_{tag}.json.gz'), 'rt'))
        ch = np.zeros(self.nK, bool)
        miss = 0
        for ds, sy, *_ in d['plain']:
            j = self.kid.get((tuple(ds), tuple(sy)))
            if j is None:
                miss += 1
            else:
                ch[j] = True
        ch |= self.kfree
        self.set_chosen(ch)
        self.lvl = self.sF.copy()
        for ds, sy, lv, *_ in d['share']:
            i = self.k5id[(tuple(ds), tuple(sy))]
            self.lvl[i] = max(self.lvl[i], lv)
        return miss
