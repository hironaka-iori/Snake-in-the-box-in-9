"""Production share encoding: wincert.Encoding plus the corner-share clauses with a STATIC cap.

ShareEncoding(window, alpha, radius, M, cap) is the CNF of s0_lean_design.md, section 4.1:

  base   wincert.Encoding (unchanged clauses and kinds, built first, same variable numbers)
  then, for each centre c = window[i] (i = 1..k) and each direction kk outside the two path
  directions of c (7 values), with q = c ^ 2^kk:
    emptyE    [X q, X q^a, X q^b, X q^ab, E[q,ab]]           for the 28 pairs ab avoiding kk
              (itertools.combinations order = freePairs kk kk)
    totUp     totalizer eTot_q over the 28 E's (upward clauses, all 28 outputs)
    totDown   totalizer dTot_q over the 9 primaries X(q ^ 2^t), t = 0..8 (downward clauses)
    shareCl   u[q,t], t = 1..tmax_q, tmax_q = min(cap + 1, 28 M):
              for dd = 1..9 with cneed = ceil(t dd / M) <= 28:
              [u] + ([-eTot_q[cneed]] if cneed >= 1) + ([dTot_q[dd+1]] if dd <= 8)
  and finally
    totUp     cap totalizer over all u (in that order), outputs truncated at cap + 1
              (clause o[i+j] <- a[i] & b[j] only for i + j <= cap + 1; complete for >= cap+1)
    shareCap  the unit [-capTot[cap+1]]

In every configuration of the local model, u[q,t] is forced for t <= floor(M e0(q) / d(q)), so
UNSAT of the static CNF proves  sum_centres shareN_M >= cap + 1  (RefutedShare W bounds M cap).
Cycle cuts are added lazily (kind 'cycle_cut') exactly as in wincert.decide; the final clause
set (with cuts) is the committed certificate CNF.

Metadata for a Lean generator: self.sq[(q, a, b)] = E variable, self.tots = list of literal
lists (one per totalizer: per q the eTot then dTot, last the cap totalizer), self.qs = list of
dicts {c, kk, q, eT, dT, tmax, u: [...]}, self.capT = index of the cap totalizer.
"""
import itertools, os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
import wincert
from wincert import window_from_dirs, cycles_of
from pysat.solvers import Cadical153


def ceil_div(a, b):
    return -(-a // b)


class ShareEncoding(wincert.Encoding):
    def __init__(self, window, alpha, radius, M, cap, ends=2):
        self.M, self.cap = M, cap
        super().__init__(window, alpha, radius, ends)

    # ------------------------------------------------------------------ build
    def build(self):
        super().build()
        self.nbase_clauses, self.nbase_vars = len(self.clauses), self.nv
        self.build_share()

    def totalizer(self, lits, up=True, down=False, limit=None, kind_up='totUp', kind_down='totDown'):
        """Totalizer outputs o[1..n'] (o[c] <-> #true >= c in the requested directions);
        with `limit`, outputs above `limit` are not created (upward clauses only)."""
        lim = limit if limit is not None else len(lits)

        def rec(ls):
            if len(ls) == 1:
                return [None, ls[0]]
            a = rec(ls[:len(ls) // 2]); b = rec(ls[len(ls) // 2:])
            na, nb = len(a) - 1, len(b) - 1
            no = min(na + nb, lim)
            o = [None] + [self.fresh() for _ in range(no)]
            for i in range(na + 1):
                for j in range(nb + 1):
                    if up and 0 < i + j <= no:
                        c = [o[i + j]]
                        if i: c.append(-a[i])
                        if j: c.append(-b[j])
                        self.add(c, kind_up)
                    if down and i + j + 1 <= no:
                        c = [-o[i + j + 1]]
                        if i + 1 <= na: c.append(a[i + 1])
                        if j + 1 <= nb: c.append(b[j + 1])
                        self.add(c, kind_down)
            return o
        self.tots.append(list(lits))
        return rec(list(lits))

    def build_share(self):
        X, B, M, cap = self.var, self.B, self.M, self.cap
        w = self.window
        self.sq, self.tots, self.qs, self.ulits = {}, [], [], []
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
                    assert all(v in B for v in sq), 'radius too small for the share'
                    e = self.fresh(); Es.append(e); self.sq[(q, a, b)] = e
                    self.add([X[v] for v in sq] + [e], 'emptyE')
                nb = [q ^ 1 << t for t in range(9)]
                assert all(v in B for v in nb)
                eT = len(self.tots); ge_e = self.totalizer(Es, up=True)
                dT = len(self.tots); ge_d = self.totalizer([X[v] for v in nb], up=False, down=True)
                nE = len(Es)
                tmax = min(cap + 1, M * nE)
                us = []
                for t in range(1, tmax + 1):
                    u = self.fresh(); us.append(u)
                    for dd in range(1, 10):
                        cneed = ceil_div(t * dd, M)
                        if cneed > nE:
                            continue
                        cl = [u]
                        if cneed >= 1:
                            cl.append(-ge_e[cneed])
                        if dd <= 8:
                            cl.append(ge_d[dd + 1])
                        self.add(cl, 'shareCl')
                self.ulits += us
                self.qs.append(dict(c=ci, kk=kk, q=q, eT=eT, dT=dT, tmax=tmax, u=us))
        self.capT = len(self.tots)
        o = self.totalizer(self.ulits, up=True, limit=cap + 1)
        if len(o) - 1 >= cap + 1:
            self.add([-o[cap + 1]], 'shareCap')
        self.nshare_vars = self.nv - self.nbase_vars

    # ------------------------------------------------------------- evaluation
    def share_of(self, sel):
        """Exact shareN_M per centre index (over the 7 non-path neighbours) of a selection."""
        S = set(sel); per = {}
        for s in self.qs:
            q = s['q']
            if q in S:
                continue
            e0 = sum(1 for a, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            per[s['c']] = per.get(s['c'], 0) + (self.M * e0) // d
        return per

    def alpha_of(self, sel):
        S = set(sel); w = self.window; out = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
            out.append(sum(1 for a, b in itertools.combinations(range(9), 2)
                           if a not in used and b not in used and (c ^ 1 << a ^ 1 << b) not in S))
        return out


def alpha_arg(al):
    """Key ranges ((lo,hi),...) -> wincert alpha arguments (int when lo == hi)."""
    return [a[0] if a[0] == a[1] else tuple(a) for a in al]


def from_key(key, M=12, cap=None, radius=4):
    ds, al = key
    w = window_from_dirs(list(ds))
    if cap is None:
        return wincert.Encoding(w, alpha_arg(al), radius)
    return ShareEncoding(w, alpha_arg(al), radius, M, cap)


def share_exact(enc_or_window, sel, M=12):
    """Exact window shareN for a selection (works for a plain Encoding too)."""
    w = enc_or_window.window if hasattr(enc_or_window, 'window') else enc_or_window
    S = set(sel); tot = 0
    for ci in range(1, len(w) - 1):
        c = w[ci]
        used = {(c ^ w[ci - 1]).bit_length() - 1, (c ^ w[ci + 1]).bit_length() - 1}
        for kk in range(9):
            if kk in used:
                continue
            q = c ^ 1 << kk
            if q in S:
                continue
            e0 = sum(1 for a, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a, q ^ 1 << b, q ^ 1 << a ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            tot += (M * e0) // d
    return tot


def solve(enc, time_limit=60.0, budget=20000):
    """Lazy-cut solve of the static clause set.  Returns (status, selection or None, cuts, seconds);
    status in UNSAT / SAT / TIMEOUT.  Cuts are appended to enc.clauses (kind cycle_cut)."""
    t0 = time.time(); cuts = 0
    with Cadical153(bootstrap_with=enc.clauses) as s:
        while True:
            if time.time() - t0 > time_limit:
                return 'TIMEOUT', None, cuts, time.time() - t0
            s.conf_budget(budget)
            ok = s.solve_limited()
            if ok is None:
                continue
            if not ok:
                return 'UNSAT', None, cuts, time.time() - t0
            m = s.get_model()
            sel = [v for v in enc.ball if m[enc.var[v] - 1] > 0]
            cyc = cycles_of(sel)
            if not cyc:
                return 'SAT', sel, cuts, time.time() - t0
            for c in cyc:
                enc.add_cycle_cut(c); cuts += 1
                s.add_clause(enc.clauses[-1])


FSIZE_KB = 300 * 1024      # proof files are capped at 300 MB (disk budget)
CADICAL = os.environ.get('CADICAL', '/home/user/lean-deps/toolchain/lean-4.19.0-linux/bin/cadical')


def measure_proof(enc, workdir, timeout=900, drat_check=False):
    """Cold solves of the static CNF (with the cuts found) by the CaDiCaL binary:
    DRAT size/time, then --lrat trimmed to the empty clause's dependencies (hints = what the
    Lean replay checks).  Every proof file is deleted right after it is measured."""
    sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
    from gen_lean_core import trim_lrat
    os.makedirs(workdir, exist_ok=True)
    cnf = os.path.join(workdir, 'm.cnf'); drat = os.path.join(workdir, 'm.drat')
    raw = os.path.join(workdir, 'm.raw.lrat'); trimmed = os.path.join(workdir, 'm.lrat')
    wincert.write_cnf(enc, cnf)
    out = {'variables': enc.nv, 'clauses': len(enc.clauses), 'cnf_bytes': os.path.getsize(cnf)}
    try:
        t = time.time()
        r = subprocess.run(['bash', '-c', f'ulimit -f {FSIZE_KB}; exec nice -n 19 {CADICAL} -q --no-binary {cnf} {drat}'],
                           capture_output=True, text=True, timeout=timeout)
        out['drat_seconds'] = round(time.time() - t, 1); out['drat_rc'] = r.returncode
        out['drat_bytes'] = os.path.getsize(drat)
        if r.returncode not in (20,):
            out['failed'] = 'drat run rc %d (file cap?)' % r.returncode
            return out
        out['drat_lines'] = sum(1 for _ in open(drat, 'rb'))
        if drat_check:
            t = time.time()
            r2 = subprocess.run(['nice', '-n', '19', wincert.ensure_drat(), cnf, drat, '-t', str(timeout)],
                                capture_output=True, text=True, timeout=timeout + 60)
            out['drat_trim_verified'] = 's VERIFIED' in r2.stdout
            out['drat_trim_seconds'] = round(time.time() - t, 1)
        os.remove(drat)
        t = time.time()
        r = subprocess.run(['bash', '-c', f'ulimit -f {FSIZE_KB}; exec nice -n 19 {CADICAL} -q --lrat --no-binary {cnf} {raw}'],
                           capture_output=True, text=True, timeout=timeout)
        out['lrat_seconds'] = round(time.time() - t, 1)
        out['lrat_raw_bytes'] = os.path.getsize(raw)
        if r.returncode != 20:
            out['failed'] = 'lrat run rc %d (file cap?)' % r.returncode
            return out
        nl, nh, core = trim_lrat(raw, trimmed, len(enc.clauses))
        os.remove(raw)
        out.update(lrat_lemmas=nl, lrat_hints=nh, core_clauses=len(core), lrat_trim_bytes=os.path.getsize(trimmed))
        kinds = {}
        for i in core:
            k = enc.kinds[i - 1]; k = k.split('@')[0]
            kinds[k] = kinds.get(k, 0) + 1
        out['core_kinds'] = kinds
    except subprocess.TimeoutExpired:
        out['timeout'] = True
    finally:
        for p in (cnf, drat, raw, trimmed):
            if os.path.exists(p):
                os.remove(p)
    return out


if __name__ == '__main__':
    # smoke test: python wincert_share.py '0,1,2,3,0,4' '2-2,6-21,2-2,4-4,6-21' cap
    ds = tuple(int(x) for x in sys.argv[1].split(','))
    al = tuple(tuple(int(y) for y in x.split('-')) for x in sys.argv[2].split(','))
    cap = int(sys.argv[3])
    t = time.time(); enc = from_key((ds, al), cap=cap)
    print('built', enc.nv, 'vars', len(enc.clauses), 'clauses', f'{time.time()-t:.1f}s', flush=True)
    st, sel, cuts, sec = solve(enc, float(sys.argv[4]) if len(sys.argv) > 4 else 120)
    print(st, cuts, round(sec, 1), share_exact(enc, sel) if sel else '')
