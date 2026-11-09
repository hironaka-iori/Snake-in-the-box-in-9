"""Share refinement on the k6 FULL product (stage B/C solver side).

Weight 120 A + S5 (comb.py), every known plain exclusion.  Each round: Howard's minimum cycle; for
each distinct window on it, cheapest first:
  1. 6-window plain status unknown          -> plain test (UNSAT removes its transitions);
  2. 5-window never solved                  -> plain test (UNSAT removes; SAT gives a witness ub);
  3. 5-window share below its witness       -> threshold at the next level above lb (LEVELS),
     below the smallest timed-out level and <= ub; UNSAT raises S5 on every transition with
     that trailing 5-window.
A round that can test nothing on its cycle is an obstruction of the current data (every window
plain-SAT and every share at its witness or at a timed-out level): logged, then the loop retries
the timed-out levels once with a long time limit (TLLONG) before stopping.
Each round is one line of data/loop_rounds.jsonl; every solver call is logged by solvers.py.
usage: nice -n 10 python loop.py HOURS [TL] [TLLONG]
"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import solvers as SV

LEVELS = [16, 24, 48, 72, 108, 150, 200]
INF = 10 ** 6
ROUNDS = os.path.join(HERE, 'data', 'loop_rounds.jsonl')


class State:
    def __init__(self):
        self.G = C.build('all', with_share=True, with_w3=False)
        self.Pr = C.fp.Product()
        self.ok = np.ones(len(self.G['U']), bool)
        self.S = C.fp.Status()
        for k in C.own_plain_unsat():
            self.S.st[k] = 'UNSAT'
        self.O = C.share_records()
        self.long_tried = set()

    def positions(self, k):
        g = np.unique(self.Pr.edges_of(k))
        p = np.searchsorted(self.G['G'], g)
        m = p < len(self.G['G'])
        p, g = p[m], g[m]
        return p[self.G['G'][p] == g]

    def exclude(self, k):
        self.ok[self.positions(k)] = False
        self.S.st[k] = 'UNSAT'

    def raise_share(self, k, T):
        p = self.positions(k)
        self.G['S5'][p] = np.maximum(self.G['S5'][p], T)

    def share_state(self, k):
        return self.O.get(C.rkey_of(k))

    def evaluate(self):
        idx = np.nonzero(self.ok)[0]
        U = self.G['U'][idx].astype(np.int64); V = self.G['V'][idx].astype(np.int64)
        m = C.prune(int(self.G['n']), U, V)
        L = idx[m]
        w = 120 * self.G['A'][L].astype(np.int64) + self.G['S5'][L]
        mu, cyc = C.howard(int(self.G['n']), self.G['U'][L], self.G['V'][L], w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        return lam, [int(L[e]) for e in cyc], len(L)


def next_T(s):
    if s['lb'] >= s['ub']:
        return None
    for L in LEVELS:
        if s['lb'] < L <= s['ub'] and L < s['fail']:
            return L
    if s['ub'] < INF and s['lb'] < s['ub'] < s['fail']:
        return s['ub']
    return None


def apply_share(st, k, r):
    st.O.apply(r)
    if r['result'] == 'UNSAT':
        st.raise_share(k, r['T'])


def round_(st, tl, tllong):
    t0 = time.time()
    lam, cyc, nlive = st.evaluate()
    rec = dict(time=time.strftime('%H:%M:%S'), lam=str(lam), mu=float(lam) / 120,
               m_real=C.bound_real(float(lam), 1, 0, 0), len=len(cyc), live=nlive)
    tests = []; seen = set()
    progress = False
    for e in cyc:
        ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
        if (k5, k6) in seen:
            continue
        seen.add((k5, k6))
        if st.S.st.get(k6) is None:
            r = SV.plain(k6, tl=tl / 2); tests.append(('p6', r['result'], r['seconds']))
            st.S.st[k6] = r['result']
            if r['result'] == 'UNSAT':
                st.exclude(k6); progress = True
                continue
        if st.S.st.get(k5) == 'UNSAT':
            st.exclude(k5); progress = True; continue
        s = st.share_state(k5)
        if not s.get('tested') and st.S.st.get(k5) is None:
            r = SV.plain(k5, tl=tl / 2); tests.append(('p5', r['result'], r['seconds']))
            st.S.st[k5] = r['result']
            if r['result'] == 'UNSAT':
                st.exclude(k5); progress = True
                continue
            if r['result'] == 'SAT':
                st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
        need = (float(lam) + 4) * 1 - 120 * int(st.G['A'][e])
        if need <= st.G['S5'][e]:
            continue
        T = next_T(s)
        if T is None:
            continue
        r = SV.share_thr(k5, T, tl=tl); tests.append(('t', T, r['result'], r['seconds']))
        apply_share(st, k5, r)
        if r['result'] == 'UNSAT':
            progress = True
    if not tests:
        # obstruction of the current data: retry timed-out levels once with a long limit
        for e in cyc:
            ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
            s = st.share_state(k5)
            if k5 in st.long_tried or s['fail'] >= INF or s['lb'] >= s['ub']:
                continue
            st.long_tried.add(k5)
            T = min(s['fail'], s['ub'])
            r = SV.share_thr(k5, T, tl=tllong); tests.append(('T', T, r['result'], r['seconds']))
            apply_share(st, k5, r)
            if r['result'] == 'UNSAT':
                progress = True
            break
    rec.update(tests=tests, n_tests=len(tests), progress=progress, s=round(time.time() - t0, 1),
               cycle=[dict(A=int(st.G['A'][e]), S5=int(st.G['S5'][e])) for e in cyc])
    return rec


def main():
    hours = float(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 60
    tllong = float(sys.argv[3]) if len(sys.argv) > 3 else 900
    st = State()
    t_end = time.time() + hours * 3600
    rnd = 0
    stuck = 0
    while time.time() < t_end:
        rec = round_(st, tl, tllong)
        rec['round'] = rnd; rnd += 1
        C.log(f"round {rnd}: lambda {rec['lam']} = {rec['mu']:.4f} m<={rec['m_real']:.3f} len {rec['len']} "
              f"tests {rec['tests']} [{rec['s']}s]")
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        stuck = 0 if rec['n_tests'] else stuck + 1
        if stuck >= 2:
            C.log('stuck: no test possible on the minimum cycle'); break


if __name__ == '__main__':
    main()
