"""Exact minimum of the window charge  sum_{centres} c  for direction-only windows (radius 4).

A key is (canonical direction sequence, alpha ranges); alpha (0,21) means unconstrained.
Search per key (incremental, one CaDiCaL instance): build the W3 CNF with a generous cap
(the plain witness), then descend: assume the totalizer output  -o[T - 168k]  (sum <= T-1);
SAT -> a witness with smaller exact charge (ub), UNSAT -> lb = T.  Cycle cuts are kept.
On a timeout the search bisects between lb and ub.  Every solver call is one line of the oracle
file (resumable); a key is settled when lb == ub.

usage: survey.py K [--tl 300] [--key-hours 1.0] [--oracle FILE]
"""
import argparse, itertools, json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
from w3enc import W3Encoding, window_from_dirs, cycles_of
from pysat.solvers import Cadical153

ORACLE = os.path.join(HERE, 'data', 'w3_oracle.jsonl')
FREE = (0, 21)
START_PER_CENTRE = 330          # initial totalizer reach (27.5 w_3 per centre)


def canon(ds):
    m, r = {}, []
    for d in ds:
        m.setdefault(d, len(m)); r.append(m[d])
    return tuple(r)


def induced(ds):
    vs = [0]
    for d in ds:
        vs.append(vs[-1] ^ (1 << d))
    return len(set(vs)) == len(vs) and all(bin(vs[i] ^ vs[j]).count('1') != 1
                                           for i in range(len(vs)) for j in range(i + 2, len(vs)))


def key(ds, al):
    al = tuple(tuple(a) for a in al)
    f = (canon(ds), al)
    r = (canon(tuple(reversed(ds))), tuple(reversed(al)))
    return min(f, r)


def shapes(k):
    """Canonical induced direction sequences of length k+1, up to relabelling and reversal."""
    out = set()
    for ds in itertools.product(range(k + 1), repeat=k + 1):
        if canon(ds) == ds and induced(ds):
            out.add(key(ds, [FREE] * k)[0])
    return sorted(out)


def alpha_arg(al):
    return [None if tuple(a) == FREE else (a[0] if a[0] == a[1] else tuple(a)) for a in al]


def mem_ok():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable'):
            return int(line.split()[1]) / 1e6
    return 99


def wait_mem():
    while mem_ok() < 3.0:
        print(f'   low memory ({mem_ok():.1f} GB available), pausing', flush=True)
        time.sleep(60)


class Oracle:
    def __init__(self, path=ORACLE):
        self.path = path
        self.st = {}
        if os.path.exists(path):
            for l in open(path):
                self.apply(json.loads(l))

    def get(self, k):
        return self.st.setdefault(k, dict(lb=0, ub=None, fail=None, excl=False))

    def apply(self, r):
        k = key(tuple(r['dirs']), r['alpha'])
        s = self.get(k)
        if r['result'] == 'EXCL':
            s['excl'] = True
        if r.get('witness') is not None:
            s['ub'] = r['witness'] if s['ub'] is None else min(s['ub'], r['witness'])
        if r['result'] == 'UNSAT' and r.get('T') is not None:
            s['lb'] = max(s['lb'], r['T'])
        if r['result'] == 'TIMEOUT' and r.get('T') is not None:
            s['fail'] = r['T'] if s['fail'] is None else min(s['fail'], r['T'])

    def log(self, r):
        self.apply(r)
        with open(self.path, 'a') as f:
            f.write(json.dumps(r) + '\n')

    def settled(self, k):
        s = self.get(k)
        return s['excl'] or (s['ub'] is not None and s['lb'] >= s['ub'])


def solve_assume(s, enc, assum, tl, budget=20000):
    t0 = time.time(); cuts = 0
    while True:
        if time.time() - t0 > tl:
            return 'TIMEOUT', None, cuts, time.time() - t0
        s.conf_budget(budget)
        ok = s.solve_limited(assumptions=assum)
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


class IncW3(W3Encoding):
    """W3 encoding without the cap unit (self.noUnit); root_outputs[j] <-> sum_y >= j for
    j <= cap - 168 k + 1, used as assumptions."""
    noUnit = True


def search(k, O, tl, key_seconds, lb_floor=0, verbose=True):
    """Descending search for the exact minimum charge of key k = (dirs, alpha)."""
    ds, al = k
    w = window_from_dirs(list(ds)); nc = len(w) - 2
    s = O.get(k)
    base = dict(dirs=list(ds), alpha=[list(a) for a in al])
    t_end = time.time() + key_seconds
    if s['ub'] is None and not s['excl']:
        wait_mem()
        enc = W3Encoding(w, alpha_arg(al), 4, None)
        st, sel, cuts, sec = w3enc.solve(enc, tl)
        r = dict(base, T=None, result='EXCL' if st == 'UNSAT' else st,
                 witness=w3enc.window_charge(w, sel) if sel else None, seconds=round(sec, 1), cuts=cuts)
        O.log(r)
        if verbose:
            print(f'  plain {ds} {[a[0] for a in al]}: {r["result"]} w={r["witness"]} {r["seconds"]}s', flush=True)
        if st != 'SAT':
            return
    if O.settled(k):
        return
    wait_mem()
    t0 = time.time()
    enc = IncW3(w, alpha_arg(al), 4, min(s['ub'], START_PER_CENTRE * nc))
    root = enc.root_outputs
    build = time.time() - t0
    lb = max(s['lb'], lb_floor)
    with Cadical153(bootstrap_with=enc.clauses) as sv:
        ncl0 = len(enc.clauses)
        while time.time() < t_end:
            s = O.get(k); ub, lb = s['ub'], max(s['lb'], lb_floor)
            if lb >= ub:
                break
            fail = s['fail']
            hi = ub if fail is None else min(fail, ub)
            T = (lb + hi + 1) // 2                  # bisection; SAT witnesses usually fall far below T
            if T <= lb:
                break
            if T > enc.cap + 1:
                T = enc.cap + 1
            idx = T - 168 * nc                    # sum_y <= T - 1 - 168 nc  <=>  -o[idx]
            assum = [-root[idx]] if 1 <= idx < len(root) else []
            if idx < 1:
                st, sel, cuts, sec = 'UNSAT', None, 0, 0.0
            else:
                st, sel, cuts, sec = solve_assume(sv, enc, assum, min(tl, max(5, t_end - time.time())))
            wv = w3enc.window_charge(w, sel) if sel else None
            r = dict(base, T=T, result=st, witness=wv, seconds=round(sec, 1), cuts=cuts, nv=enc.nv, sym=enc.SYM,
                     ncl=len(enc.clauses) + 1, build=round(build, 1))
            O.log(r)
            if verbose:
                print(f'  T={T} {ds} {[a[0] for a in al]}: {st} w={wv} lb={O.get(k)["lb"]} {r["seconds"]}s', flush=True)


SINGLE_LB = 257       # proved minimum of c at one internal vertex (direction-only, radius 4)


def floor_of(k, O):
    """Rigorous lower bound for a key from single-centre results: sum over centres of the
    single-centre lb for the centre's alpha range (or of the direction-only lb)."""
    ds, al = k
    tot = 0
    for a in al:
        best = SINGLE_LB
        for kk, s in O.st.items():
            if len(kk[0]) == 2 and kk[1][0][0] <= a[0] and a[1] <= kk[1][0][1]:
                best = max(best, s['lb'])
        tot += best
    return tot


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('--alphas', default=None, help="single centre: comma list of alpha ranges, e.g. 1-1,2-2,6-21")
    ap.add_argument('--tl', type=float, default=300)
    ap.add_argument('--key-hours', type=float, default=1.0)
    ap.add_argument('--oracle', default=ORACLE)
    a = ap.parse_args()
    O = Oracle(a.oracle)
    if a.alphas:
        for x in a.alphas.split(','):
            lo, hi = map(int, x.split('-'))
            k = key((0, 1), [(lo, hi)])
            print(f'single alpha {lo}-{hi}', flush=True)
            search(k, O, a.tl, a.key_hours * 3600, floor_of(k, O))
            print(f'single alpha {lo}-{hi}: lb {O.get(k)["lb"]} ub {O.get(k)["ub"]}', flush=True)
        return
    for ds in shapes(a.k):
        k = key(ds, [FREE] * a.k)
        print(f'shape {ds}', flush=True)
        search(k, O, a.tl, a.key_hours * 3600, floor_of(k, O))
        s = O.get(k)
        print(f'shape {ds}: lb {s["lb"]} ub {s["ub"]} ({s["lb"]/12/a.k:.3f}..{(s["ub"] or 0)/12/a.k:.3f} w3/centre)', flush=True)


if __name__ == '__main__':
    main()
