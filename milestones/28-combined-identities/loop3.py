"""Refinement toward 232: loop.py on one core, plus context share thresholds (share7.py).

Weight 120 A + S5 on the k6 full product, every known plain exclusion and share bound (milestone 28
data plus this section's files).  Each round takes Howard's minimum cycle; for each distinct step
window on it (binding-cycle keys first), cheapest first:
  1. 6-window plain status unknown     -> plain test in the step's orientation (UNSAT excludes; a SAT
                                          model also gives the ctx-7 trailing-share witness);
  2. 5-window never solved             -> plain test;
  3. need = lambda + 4 - 120 A > S5:
     a. 5-window threshold at the next level above lb (below its witness and its timed-out level);
     b. else a ctx-7 threshold (7 directions, share on the trailing 5 centres) at the next level
        above the step's current S5;
     c. else (CTX8=1) a ctx-8 threshold.
If a round can test nothing, timed-out levels are retried once with TLLONG.
New calls: data/oracle_plain_r232.jsonl, data/oracle_share_r232.jsonl, data/oracle_share7_r232.jsonl;
rounds: data/loop232_rounds.jsonl.
usage: nice -n 10 python loop3.py HOURS [TL] [TLLONG]
"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import comb as C
import solvers as SV
import share7 as S7
import loop as LP
import wincert_share as ws

SV.OPL = os.path.join(HERE, 'data', 'oracle_plain_r232.jsonl')
SV.OSH = os.path.join(HERE, 'data', 'oracle_share_r232.jsonl')
ROUNDS = os.path.join(HERE, 'data', 'loop232_rounds.jsonl')
LEVELS = [16, 24, 32, 48, 60, 72, 90, 108, 150, 200]
LEVELS5 = [16, 24, 48, 72, 108, 150, 200]
CTX8 = os.environ.get('CTX8', '1') == '1'
INF = 10 ** 6


def plain_fwd(ds, t, tl):
    """Plain test of the window (ds, lumped counts t) in the given orientation; SAT models of
    6-count windows also give the ctx-7 trailing-share witness."""
    SV.wait_mem()
    al = tuple(C.LUMP[s] for s in t)
    enc = ws.from_key((tuple(ds), al))
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(ds), alpha=[list(a) for a in al], kind='plain', k=len(al), result=st,
             witness=ws.share_exact(enc, sel, 12) if sel else None, cuts=cuts, seconds=round(sec, 2),
             nv=enc.nv, ncl=len(enc.clauses))
    SV._append(SV.OPL, r)
    if sel and len(t) == 6:
        r5 = S7.trailing_share(enc.window, sel)
        rc = dict(dirs=list(ds), t=list(t), ctx=7, T=None, kind='plain_ctx', result='SAT', witness5=r5,
                  seconds=r['seconds'])
        SV._append(S7.FILE, rc)
        r['witness5'] = r5
    return r


class State(LP.State):
    def __init__(self):
        super().__init__()
        self.X = S7.Ctx()
        self.I = S7.ctx_index(self.Pr, C.canon)

    def ctx_positions(self, ctx, c, t):
        return S7.positions(self.G, self.I, ctx, c, t, C.GA.cnt_idx, C.NT, np)

    def ctx_apply(self, r):
        self.X.apply(r)
        if r['result'] == 'UNSAT':
            p = self.ctx_positions(r['ctx'], tuple(r['dirs']), tuple(r['t']))
            self.G['S5'][p] = np.maximum(self.G['S5'][p], r['T'])


def next_level(cur, s, levels=LEVELS):
    for L in levels:
        if L > cur and L > s['lb'] and L <= s['ub'] and L < s['fail']:
            return L
    if s['ub'] < INF and s['ub'] > cur and s['ub'] < s['fail']:
        return s['ub']
    return None


def round_(st, tl, tllong):
    t0 = time.time()
    lam, cyc, nlive = st.evaluate()
    t_eval = time.time() - t0
    rec = dict(time=time.strftime('%H:%M:%S'), lam=str(lam), mu=float(lam) / 120,
               m_real=C.bound_real(float(lam), 1, 0, 0), len=len(cyc), live=nlive, eval_s=round(t_eval, 1))
    tests = []; seen = set(); progress = False
    later = []
    for e in cyc:
        g = int(st.G['G'][e])
        ds, t, k5, k6 = C.step_windows(g, st.Pr)
        if (k5, k6) in seen:
            continue
        seen.add((k5, k6))
        if not st.ok[e]:
            continue
        if st.S.st.get(k6) is None:
            r = plain_fwd(C.canon(ds[1:8]), t, tl / 2); tests.append(('p6', r['result'], r['seconds']))
            st.S.st[k6] = r['result']
            if r['result'] == 'UNSAT':
                st.exclude(k6); progress = True; continue
            if r['result'] == 'SAT':
                st.X.apply(dict(dirs=list(C.canon(ds[1:8])), t=list(t), ctx=7, result='SAT', witness5=r['witness5']))
        if st.S.st.get(k5) == 'UNSAT':
            st.exclude(k5); progress = True; continue
        s = st.share_state(k5)
        if not s.get('tested') and st.S.st.get(k5) is None:
            r = SV.plain(k5, tl=tl / 2); tests.append(('p5', r['result'], r['seconds']))
            st.S.st[k5] = r['result']
            if r['result'] == 'UNSAT':
                st.exclude(k5); progress = True; continue
            if r['result'] == 'SAT':
                st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
        need = float(lam) + 4 - 120 * int(st.G['A'][e])
        cur = int(st.G['S5'][e])
        if need <= cur:
            continue
        T = LP.next_T(s)
        if T is not None and T > cur:
            r = SV.share_thr(k5, T, tl=tl); tests.append(('t', T, r['result'], r['seconds']))
            LP.apply_share(st, k5, r)
            if r['result'] == 'UNSAT':
                progress = True
            continue
        later.append((e, ds, t, need))
    # context thresholds, after the cheaper tests of the round
    for e, ds, t, need in later:
        cur = int(st.G['S5'][e])
        if need <= cur:
            continue
        for ctx in ((7, 8) if CTX8 else (7,)):
            c = C.canon(ds[8 - ctx:])
            sx = st.X.get((ctx, c, tuple(t)))
            T = next_level(cur, sx)
            if T is None:
                continue
            r = S7.thr(c, t, T, ctx, tl=tl); tests.append((f'c{ctx}', T, r['result'], r['seconds']))
            st.ctx_apply(r)
            if r['result'] == 'UNSAT':
                progress = True
            break
    if not tests:
        # obstruction of the current data: retry one timed-out level with a long limit
        for e in cyc:
            ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
            cur = int(st.G['S5'][e])
            cands = []
            s = st.share_state(k5)
            if ('5', k5) not in st.long_tried and s['fail'] < INF and s['lb'] < s['ub'] and s['fail'] > cur:
                cands.append(('5', k5, min(s['fail'], s['ub'])))
            for ctx in (7, 8):
                c = C.canon(ds[8 - ctx:])
                sx = st.X.get((ctx, c, tuple(t)))
                if (ctx, c, t) not in st.long_tried and sx['fail'] < INF and sx['fail'] > cur and sx['fail'] <= sx['ub']:
                    cands.append((ctx, (c, t), sx['fail']))
            if not cands:
                continue
            kind, k, T = min(cands, key=lambda z: z[2])
            if kind == '5':
                st.long_tried.add(('5', k))
                r = SV.share_thr(k, T, tl=tllong); tests.append(('T', T, r['result'], r['seconds']))
                LP.apply_share(st, k, r)
            else:
                st.long_tried.add((kind, k[0], k[1]))
                r = S7.thr(k[0], k[1], T, kind, tl=tllong); tests.append((f'C{kind}', T, r['result'], r['seconds']))
                st.ctx_apply(r)
            progress = progress or r['result'] == 'UNSAT'
            break
    rec.update(tests=tests, n_tests=len(tests), progress=progress, s=round(time.time() - t0, 1),
               cycle=[[int(st.G['A'][e]), int(st.G['S5'][e])] for e in cyc])
    return rec


def main():
    hours = float(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 60
    tllong = float(sys.argv[3]) if len(sys.argv) > 3 else 900
    st = State()
    C.log(f'state ready, rss {C.rss_mb():.0f} MB')
    t_end = time.time() + hours * 3600
    rnd = sum(1 for _ in open(ROUNDS)) if os.path.exists(ROUNDS) else 0
    stuck = 0
    while time.time() < t_end:
        if C.disk_mb() < 300:
            C.log('disk below 300 MB: stop'); break
        rec = round_(st, tl, tllong)
        rec['round'] = rnd; rnd += 1
        C.log(f"round {rnd}: lambda {rec['lam']} = {rec['mu']:.4f} m<={rec['m_real']:.3f} len {rec['len']} "
              f"tests {rec['tests'][:8]} [{rec['s']}s, eval {rec['eval_s']}s]")
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        stuck = 0 if rec['n_tests'] else stuck + 1
        if stuck >= 2:
            C.log('stuck: no test possible on the minimum cycle'); break


if __name__ == '__main__':
    main()
