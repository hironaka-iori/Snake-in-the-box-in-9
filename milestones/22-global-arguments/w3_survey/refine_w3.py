"""w_3-charge refinement on the radius-4 L7 k5 K5 direction automaton (the alpha automaton of the
237/236 chain: 44,064 states, 240,729 edges, 11,425 five-centre window keys; edges are already
pruned by the radius-4 alpha exclusions).

Edge weight: T5(e) = lower bound on sum_{5 centres} c of the five-centre window ending at e,
c(x) = sum_Q floor(12/|Q cap S|) (see w3enc.py).  Two automata per round:
  * lo (rigorous): T5 = max(threshold lb of the key, DP over sub-windows with proved lbs:
    single-centre alpha-conditioned minima, direction-only pair/triple/five-centre minima);
  * hi (ceiling):  T5 = best SAT witness of the key (+inf when untested).
lambda = min cycle mean of T5;  mu = lambda/5 per vertex (c units, 12 c = 1 w_3);
implied bound  m <= 5 + (5 (64512 - 336) + R) / lambda  (shape_aut.bound).

Each round, every window on the lo cycle (and the hi cycle) gets one threshold test (static cap
CNF, cap = T - 1): UNSAT -> lb = T; SAT -> ub = exact charge of the witness; TIMEOUT -> fail.
T ladder (per centre): first 284, then 292, 300, 310, 322; after a timeout the highest
lower level (278, 272); finally the ub.
State: data/w3_alpha_oracle.jsonl (one line per call), data/w3_rounds.jsonl.
usage: refine_w3.py --hours 3 [--tl 120]
"""
import argparse, json, os, pickle, sys, time
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
from refine import howard, prune
import w3enc
import w3survey as survey
from w3survey import key, FREE, alpha_arg
from shape_aut import bound

SCR = os.environ.get('STAGE3', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/stage3')
PROOF = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/w3/proof'
ORACLE = os.path.join(HERE, 'data', 'w3_alpha_oracle.jsonl')
ROUNDS = os.path.join(HERE, 'data', 'w3_rounds.jsonl')
LEVELS = [272, 278, 284, 292, 300, 310, 322]
FIRST = 284          # first test per centre; lower levels only after a timeout
INF = 10 ** 6
K = 5


def load_compact():
    z = np.load(os.path.join(SCR, 'aut_compact.npz'))
    keys = pickle.load(open(os.path.join(SCR, 'aut_keys.pkl'), 'rb'))
    return int(z['n']), z['U'], z['V'], z['S'], z['KI'], keys


class Sub:
    """Proved lower bounds of sub-windows from the direction-only / single-centre oracle."""
    def __init__(self):
        self.O = survey.Oracle()
        self.single = {}
        for kk, s in self.O.st.items():
            if len(kk[0]) == 2:
                self.single[kk[1][0]] = max(s['lb'], survey.SINGLE_LB)
        self.cache = {}

    def single_lb(self, a):
        best = survey.SINGLE_LB
        for r, v in self.single.items():
            if r[0] <= a[0] and a[1] <= r[1]:
                best = max(best, v)
        return best

    def sub_lb(self, ds, al):
        if len(al) == 1:
            return self.single_lb(al[0])
        s = self.O.st.get(key(ds, [FREE] * len(al)))
        return s['lb'] if s else 0

    def floor5(self, k):
        if k in self.cache:
            return self.cache[k]
        ds, al = k
        f = [0] + [-1] * K
        for i in range(1, K + 1):
            for j in range(i):
                f[i] = max(f[i], f[j] + self.sub_lb(ds[j:i + 1], al[j:i]))
        self.cache[k] = f[K]
        return f[K]


class W3Oracle:
    def __init__(self):
        self.st = {}
        if os.path.exists(ORACLE):
            for l in open(ORACLE):
                self.apply(json.loads(l))

    def get(self, k):
        return self.st.setdefault(k, dict(lb=0, ub=INF, fail=INF, excl=False, tested=False))

    def apply(self, r):
        k = key(tuple(r['dirs']), r['alpha'])
        s = self.get(k); s['tested'] = True
        if r['result'] == 'UNSAT':
            s['lb'] = max(s['lb'], r['T'])
        elif r['result'] == 'SAT':
            s['ub'] = min(s['ub'], r['witness'])
        elif r['result'] == 'TIMEOUT':
            s['fail'] = min(s['fail'], r['T'])

    def next_T(self, k, floor):
        s = self.get(k)
        lb = max(s['lb'], floor)
        if lb >= s['ub']:
            return None
        cand = [K * L for L in LEVELS if K * L > lb and K * L < s['fail']]
        if cand:
            pref = [c for c in cand if c >= K * FIRST]
            T = pref[0] if pref else cand[-1]
            return min(T, s['ub']) if s['ub'] < INF else T
        if s['ub'] < INF and s['ub'] < s['fail']:
            return s['ub']
        return None


N_UNSAT = 0


def run_test(k, T, tl, measure_every):
    survey.wait_mem()
    t0 = time.time()
    ds, al = k
    w = w3enc.window_from_dirs(list(ds))
    enc = w3enc.W3Encoding(w, alpha_arg(al), 4, T - 1)
    build = time.time() - t0
    st, sel, cuts, sec = w3enc.solve(enc, tl)
    r = dict(dirs=list(ds), alpha=[list(a) for a in al], T=T, result=st,
             witness=w3enc.window_charge(w, sel) if sel else None, cuts=cuts, seconds=round(sec, 1),
             build=round(build, 1), nv=enc.nv, ncl=len(enc.clauses))
    global N_UNSAT
    if st == 'UNSAT':
        N_UNSAT += 1
        if measure_every and N_UNSAT % measure_every == 1:
            survey.wait_mem()
            st_ = os.statvfs('/')
            if st_.f_bavail * st_.f_frsize / 1e6 > 600:
                r['proof'] = w3enc.measure_proof(enc, PROOF, timeout=900)
                print('   proof:', json.dumps(r['proof']), flush=True)
    with open(ORACLE, 'a') as f:
        f.write(json.dumps(r) + '\n')
    return r


def evaluate(n, U, V, KI, keys, O, sub):
    lb = np.array([max(O.st[k]['lb'] if k in O.st else 0, sub.floor5(k)) for k in keys], np.int64)
    ub = np.array([O.st[k]['ub'] if k in O.st else INF for k in keys], np.int64)
    out = {}
    for name, T5 in (('lo', lb), ('hi', ub)):
        w = T5[KI]
        _, cyc = howard(n, U, V, w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        out[name] = dict(lam=str(lam), mu=float(lam) / K, w3=float(lam) / K / 12, m_le=bound(float(lam), K),
                         keys=[int(KI[e]) for e in cyc], finite=bool(w[cyc].max() < INF), len=len(cyc))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--hours', type=float, default=3.0)
    ap.add_argument('--tl', type=float, default=120.0)
    ap.add_argument('--measure-every', type=int, default=8)
    ap.add_argument('--rounds', type=int, default=10000)
    a = ap.parse_args()
    t_end = time.time() + a.hours * 3600
    n, U, V, S, KI, keys = load_compact()
    sub = Sub(); O = W3Oracle()
    print(f'automaton {n} states, {len(U)} edges, {len(keys)} keys; singles {sub.single}', flush=True)
    rnd0 = sum(1 for _ in open(ROUNDS)) if os.path.exists(ROUNDS) else 0
    for rnd in range(rnd0, rnd0 + a.rounds):
        t = time.time()
        ev = evaluate(n, U, V, KI, keys, O, sub)
        lo, hi = ev['lo'], ev['hi']
        cyc_keys = sorted(set(lo['keys']))
        if hi['finite']:
            cyc_keys += sorted(set(hi['keys']) - set(cyc_keys))
        todo = [(keys[i], O.next_T(keys[i], sub.floor5(keys[i]))) for i in cyc_keys]
        todo = [x for x in todo if x[1] is not None]
        rec = dict(round=rnd, time=time.strftime('%H:%M:%S'), lam_lo=lo['lam'], w3_lo=round(lo['w3'], 4),
                   m_lo=round(lo['m_le'], 2), lam_hi=hi['lam'] if hi['finite'] else None,
                   w3_hi=round(hi['w3'], 4) if hi['finite'] else None,
                   m_hi=round(hi['m_le'], 2) if hi['finite'] else None,
                   cycle_lo=[[list(keys[i][0]), [x[0] for x in keys[i][1]]] for i in lo['keys']],
                   cycle_lo_T5=[int(max(O.get(keys[i])['lb'], sub.floor5(keys[i]))) for i in lo['keys']],
                   cycle_hi=[[list(keys[i][0]), [x[0] for x in keys[i][1]]] for i in hi['keys']] if hi['finite'] else None,
                   todo=len(todo), keys_with_lb=sum(1 for s in O.st.values() if s['lb'] > 0),
                   keys_tested=sum(1 for s in O.st.values() if s['tested']), eval_s=round(time.time() - t, 1))
        hs = f"{hi['w3']:.4f} (m<={hi['m_le']:.2f})" if hi['finite'] else 'inf'
        print(f"round {rnd} [{rec['time']}]: lo {lo['w3']:.4f} (m<={lo['m_le']:.2f}) hi {hs} "
              f"len {lo['len']} T5 {rec['cycle_lo_T5']} todo {len(todo)} [{rec['eval_s']}s]", flush=True)
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if not todo or time.time() > t_end:
            print('stop:', 'converged' if not todo else 'time budget', flush=True)
            break
        for k, T in todo:
            if time.time() > t_end:
                break
            r = run_test(k, T, a.tl, a.measure_every); O.apply(r)
            print(f"   T={T} {k[0]} {[x[0] for x in k[1]]}: {r['result']} w={r['witness']} {r['seconds']}s "
                  f"(nv {r['nv']}, cl {r['ncl']})", flush=True)


if __name__ == '__main__':
    main()
