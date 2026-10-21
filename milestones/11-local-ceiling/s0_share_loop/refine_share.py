"""Share-aware refinement of the radius-4 L7 k5 K5 direction automaton (s0_lean_design.md, 4.3).

Edge weight (integer, units of g = 2M alpha + shareN, M = 12):
    W(e) = 10 M sym(e) + T5(key5(e)),   T5 = lb = max{K+1 : (key5, K) UNSAT}   (0 if none)
so lambda = (min cycle mean of W), mu = lambda / 120 (alpha units), and the implied bound is
    m <= 9171 / (mu + 35)       (before the potential constant C of the Lean chain).

Two automata are evaluated each round:
  * rigorous   T5 = proved lower bound lb (untested or timed-out windows: 0).
  * optimistic T5 = best witness ub (an upper bound on the window's model minimum; untested
    windows: +infinity).  Its min mean bounds from above what ANY set of 5-window share
    certificates can give on this automaton, so [lambda_lo, lambda_hi] brackets the converged value.
Windows whose plain model is UNSAT (no selection at all) remove their edges (they would need
a plain exclusion certificate; counted separately).

Each round takes the rigorous minimum cycle (and, unless --lo-only, the optimistic one) and
gives every one of its windows one test:
  first visit: plain solve (witness -> ub, or EXCL), then a threshold test at T = min(ub, 108);
  later visits: next T = min(ub, next level above lb), backing off below a timed-out level.
A threshold test is the static-cap CNF of wincert_share.ShareEncoding with cap = T - 1:
UNSAT -> lb = T; SAT -> ub = exact share of the witness; TIMEOUT -> remembered.

State: share_oracle.jsonl (one line per solver call, resumable), rounds.jsonl (one line per round).
usage: refine_share.py --hours 4 [--tl 60] [--aut PKL]
"""
import argparse, json, os, sys, time, pickle, subprocess
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
R4 = os.path.join(HERE, '..', 's0_radius4')
sys.path.insert(0, os.path.join(HERE, '..', '..', '10-window-aggregate', 'scripts'))
from refine import howard, prune, key as rkey
import wincert_share as ws

M = 12
UNIT = 10 * M            # weight of one alpha unit per edge
LEVELS = [24, 48, 72, 108, 150, 200, 260, 340]
FIRST = 108
INF = 10 ** 6
ORACLE = os.path.join(HERE, 'share_oracle.jsonl')
ROUNDS = os.path.join(HERE, 'rounds.jsonl')
SCR = os.environ.get('STAGE3', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/stage3')
DEFAULT_PKL = '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/agents/e1/aut_L7k5K5r4.pkl'


def bound_m(mu):
    return 9171 / (mu + 35)


# ---------------------------------------------------------------- automaton
def load_compact(pkl):
    """(n, U, V, S, KI, keys): edges, symbols, index of the edge's 5-window key."""
    npz = os.path.join(SCR, 'aut_compact.npz'); kp = os.path.join(SCR, 'aut_keys.pkl')
    if os.path.exists(npz) and os.path.exists(kp):
        z = np.load(npz); return int(z['n']), z['U'], z['V'], z['S'], z['KI'], pickle.load(open(kp, 'rb'))
    if not os.path.exists(pkl):     # rebuild from the radius-4 oracle cache (43 MB, a few minutes)
        sys.path.insert(0, R4)
        import automaton; automaton.PK = pkl; automaton.load()
    d = pickle.load(open(pkl, 'rb'))
    keys, idx = [], {}
    KI = np.empty(len(d['W']), np.int32)
    for e, w in enumerate(d['WIN']):
        k = w[3]
        if k not in idx:
            idx[k] = len(keys); keys.append(k)
        KI[e] = idx[k]
    os.makedirs(SCR, exist_ok=True)
    np.savez(npz, n=d['n'], U=d['U'].astype(np.int32), V=d['V'].astype(np.int32), S=d['W'].astype(np.int32), KI=KI)
    pickle.dump(keys, open(kp, 'wb'))
    return d['n'], d['U'].astype(np.int32), d['V'].astype(np.int32), d['W'].astype(np.int32), KI, keys


# ------------------------------------------------------------------- oracle
class ShareOracle:
    """Per key: lb (proved T), ub (witness share), fail (smallest timed-out T), excl, tested."""
    def __init__(self):
        self.st = {}
        self.seed_e1()
        if os.path.exists(ORACLE):
            for l in open(ORACLE):
                self.apply(json.loads(l))

    def get(self, k):
        return self.st.setdefault(k, dict(lb=0, ub=INF, fail=INF, excl=False, tested=False))

    def apply(self, r):
        k = rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha']))
        s = self.get(k); s['tested'] = True
        kind, res = r['kind'], r['result']
        if kind == 'plain':
            if res == 'UNSAT':
                s['excl'] = True
            elif res == 'SAT':
                s['ub'] = min(s['ub'], r['witness'])
        else:
            T = r['T']
            if res == 'UNSAT':
                s['lb'] = max(s['lb'], T)
            elif res == 'SAT':
                s['ub'] = min(s['ub'], r['witness'])
            elif res == 'TIMEOUT':
                s['fail'] = min(s['fail'], T)

    def seed_e1(self):
        """Results of the exploratory E1 runs (pysat ITotalizer encoding; same claims)."""
        self.seeded = 0
        for fn in ('threshold_results.jsonl', 'ceiling_results.jsonl', 'probe_results.jsonl', 'refshare_results.jsonl'):
            p = os.path.join(R4, fn)
            if not os.path.exists(p):
                continue
            for l in open(p):
                r = json.loads(l)
                if r.get('M', 12) != 12 or len(r['dirs']) != 6:
                    continue
                al = r.get('alpha') or [((6, 21) if s == '6+' else (int(s), int(s))) for s in r['alpha_req'].split(',')]
                base = dict(dirs=r['dirs'], alpha=[list(a) for a in al])
                if 'result' in r:
                    self.apply(dict(base, kind='thr', T=r['T'], result=r['result'], witness=r.get('witness')))
                elif r.get('status') == 'UNSAT_MODEL':
                    self.apply(dict(base, kind='plain', result='UNSAT'))
                else:
                    if r.get('min_lower', 0) > 0:
                        self.apply(dict(base, kind='thr', T=r['min_lower'], result='UNSAT'))
                    if r.get('witness_share') is not None:
                        self.apply(dict(base, kind='thr', T=r['witness_share'] + 1, result='SAT', witness=r['witness_share']))
                self.seeded += 1

    def next_T(self, k):
        s = self.get(k)
        if s['excl'] or s['lb'] >= s['ub']:
            return None
        if s['lb'] == 0 and s['fail'] == INF:
            return min(s['ub'], FIRST)
        up = [L for L in LEVELS if L > s['lb']]
        T = min(s['ub'], up[0]) if up else s['ub'] if s['ub'] < INF else None
        if T is None:
            return None
        if T >= s['fail']:
            cand = [L for L in LEVELS if s['lb'] < L < s['fail'] and L <= s['ub']]
            T = cand[-1] if cand else None
        return T


def mem_ok():
    for line in open('/proc/meminfo'):
        if line.startswith('MemAvailable'):
            return int(line.split()[1]) / 1e6
    return 99


def wait_mem():
    while mem_ok() < 3.0:
        print(f'   low memory ({mem_ok():.1f} GB available), pausing', flush=True)
        time.sleep(60)


N_UNSAT = 0
MEASURE_EVERY = 0
HI_TOO = True


def run_test(k, kind, T, tl):
    """One solver call, in this process (the caller runs at nice 19, single-threaded)."""
    wait_mem()
    t0 = time.time()
    base = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind=kind)
    if kind == 'plain':
        enc = ws.from_key(k)
    else:
        enc = ws.from_key(k, M=M, cap=T - 1)
        base['T'] = T
    build = time.time() - t0
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(base, result=st, witness=ws.share_exact(enc, sel, M) if sel else None, cuts=cuts,
             seconds=round(sec, 1), build=round(build, 1), nv=enc.nv, ncl=len(enc.clauses))
    global N_UNSAT
    if kind == 'thr' and st == 'UNSAT':
        N_UNSAT += 1
        if MEASURE_EVERY and N_UNSAT % MEASURE_EVERY == 1:
            wait_mem()
            pm = ws.measure_proof(enc, os.path.join(SCR, 'proof'), timeout=600)
            r['proof'] = pm
            print(f"   proof: {json.dumps(pm)}", flush=True)
    with open(ORACLE, 'a') as f:
        f.write(json.dumps(r) + '\n')
    return r


# --------------------------------------------------------------- one round
def evaluate(n, U, V, S, KI, keys, O):
    lb = np.array([O.st[k]['lb'] if k in O.st else 0 for k in keys], np.int64)
    ub = np.array([O.st[k]['ub'] if k in O.st else INF for k in keys], np.int64)
    ex = np.array([O.st[k]['excl'] if k in O.st else False for k in keys], bool)
    keep = ~ex[KI]
    m = prune(n, U[keep], V[keep]); idx = np.nonzero(keep)[0][m]
    U2, V2, K2 = U[idx], V[idx], KI[idx]
    out = {'edges': int(len(idx)), 'excluded_keys': int(ex.sum())}
    for name, T5 in (('lo', lb), ('hi', np.minimum(ub, INF))):
        w = UNIT * S[idx].astype(np.int64) + T5[K2]
        _, cyc = howard(n, U2, V2, w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        out[name] = dict(lam=str(lam), mu=float(lam) / UNIT, m_le=bound_m(float(lam) / UNIT),
                         cycle_syms=[int(S[idx][e]) for e in cyc], len=len(cyc),
                         keys=[int(K2[e]) for e in cyc], finite=bool(w[cyc].max() < INF))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--hours', type=float, default=4.0)
    ap.add_argument('--tl', type=float, default=60.0)
    ap.add_argument('--aut', default=DEFAULT_PKL)
    ap.add_argument('--rounds', type=int, default=1000)
    ap.add_argument('--measure-every', type=int, default=6)
    ap.add_argument('--lo-only', action='store_true', help='test only the rigorous cycle (no ceiling tests)')
    a = ap.parse_args()
    global MEASURE_EVERY, HI_TOO
    MEASURE_EVERY = a.measure_every
    HI_TOO = not a.lo_only
    t_end = time.time() + a.hours * 3600
    n, U, V, S, KI, keys = load_compact(a.aut)
    O = ShareOracle()
    print(f'automaton: {n} states, {len(U)} edges, {len(keys)} window keys; '
          f'oracle {len(O.st)} keys ({O.seeded} E1 records)', flush=True)
    rnd0 = sum(1 for _ in open(ROUNDS)) if os.path.exists(ROUNDS) else 0
    for rnd in range(rnd0, rnd0 + a.rounds):
        t = time.time()
        ev = evaluate(n, U, V, S, KI, keys, O)
        lo, hi = ev['lo'], ev['hi']
        cyc_keys = sorted(set(lo['keys']))
        if HI_TOO and hi['finite']:          # also lower the ceiling: test the optimistic cycle's windows
            cyc_keys += sorted(set(hi['keys']) - set(cyc_keys))
        todo = [(keys[i], O.next_T(keys[i]), not O.get(keys[i])['tested']) for i in cyc_keys]
        todo = [x for x in todo if x[1] is not None or x[2]]
        nlb = sum(1 for s in O.st.values() if s['lb'] > 0)
        rec = dict(round=rnd, time=time.strftime('%H:%M:%S'), lam_lo=lo['lam'], mu_lo=round(lo['mu'], 5),
                   m_lo=round(lo['m_le'], 3), lam_hi=hi['lam'] if hi['finite'] else None,
                   mu_hi=round(hi['mu'], 5) if hi['finite'] else None, m_hi=round(hi['m_le'], 3) if hi['finite'] else None,
                   cycle_lo=lo['cycle_syms'], cycle_lo_T5=[int(O.get(keys[i])['lb']) for i in lo['keys']],
                   cycle_hi=hi['cycle_syms'] if hi['finite'] else None, todo=len(todo),
                   keys_with_lb=nlb, keys_tested=sum(1 for s in O.st.values() if s['tested']),
                   excluded=ev['excluded_keys'], edges=ev['edges'], eval_s=round(time.time() - t, 1))
        hs = f"{hi['mu']:.4f} (m<={hi['m_le']:.2f})" if hi['finite'] else 'inf'
        print(f"round {rnd} [{rec['time']}]: lo {lo['mu']:.4f} (m<={lo['m_le']:.2f}) hi {hs} "
              f"cycle {lo['cycle_syms']} T5 {rec['cycle_lo_T5']} todo {len(todo)} lb-keys {nlb} [{rec['eval_s']}s]", flush=True)
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if not todo:
            print('converged: every window of the rigorous minimum cycle is settled', flush=True)
            break
        if time.time() > t_end:
            print('time budget reached', flush=True); break
        for k, T, first in todo:
            if time.time() > t_end:
                break
            if first:
                r = run_test(k, 'plain', None, a.tl / 2); O.apply(r)
                print(f"   plain {k[0]} {[x[0] for x in k[1]]}: {r['result']} w={r['witness']} {r['seconds']}s", flush=True)
                T = O.next_T(k)
                if T is None:
                    continue
            r = run_test(k, 'thr', T, a.tl); O.apply(r)
            print(f"   T={T} {k[0]} {[x[0] for x in k[1]]}: {r['result']} w={r['witness']} {r['seconds']}s "
                  f"(nv {r['nv']}, cl {r['ncl']})", flush=True)


if __name__ == '__main__':
    main()
