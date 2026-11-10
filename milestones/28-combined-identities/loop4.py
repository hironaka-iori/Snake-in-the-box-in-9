"""Refinement toward 231: loop3.py on 2 worker processes (same tests, same order of preference).

Per round, on the distinct step windows of Howard's minimum cycle:
  (A) untested 6-windows: plain test in the step orientation (SAT models give ctx-7 witnesses);
  (B) never-solved 5-windows: plain test;
  (C) one threshold per window with S5 < lambda + 4 - 120 A: the 5-window at its next level, or, if the
      5-window is stuck (witness or timed-out level), ctx 7 and then ctx 8 at the next level above S5;
  (D) if nothing was testable: up to 2 timed-out levels retried with TLLONG.
Fixes the second-Status reader of loop3 (all plain statuses of this milestone are loaded, so nothing
known is re-tested).  New calls: data/oracle_plain_r232b.jsonl, data/oracle_share_r232b.jsonl,
data/ctxshare_r232b.jsonl; rounds: data/loop232b_rounds.jsonl.
usage: nice -n 10 python loop4.py HOURS [TL] [TLLONG]
"""
import sys, os, json, time, glob, gzip, itertools
import multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import numpy as np
import comb as C
import solvers as SV
import share7 as S7
import loop as LP
import loop3 as L3
import wincert_share as ws

SV.OPL = os.path.join(HERE, 'data', 'oracle_plain_r232b.jsonl')
SV.OSH = os.path.join(HERE, 'data', 'oracle_share_r232b.jsonl')
CTXB = os.path.join(HERE, 'data', 'ctxshare_r232b.jsonl')
ROUNDS = os.path.join(HERE, 'data', 'loop232b_rounds.jsonl')
INF = 10 ** 6


def plain_fwd(ds, t, tl):
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
        SV._append(CTXB, dict(dirs=list(ds), t=list(t), ctx=7, T=None, kind='plain_ctx', result='SAT',
                              witness5=r5, seconds=r['seconds']))
        r['witness5'] = r5
    return r


def work(job):
    kind = job[0]
    if kind == 'p6':
        _, key, ds, t, tl = job
        return job, plain_fwd(ds, t, tl)
    if kind == 'p5':
        _, key, tl = job
        return job, SV.plain(key, tl=tl)
    if kind == 't':
        _, key, T, tl = job
        return job, SV.share_thr(key, T, tl=tl)
    _, (ctx, c, t), T, tl = job
    return job, S7.thr(c, t, T, ctx, tl=tl, path=CTXB)


class State(L3.State):
    def __init__(self):
        super().__init__()
        C.fp.K6.OPLAIN = os.path.join(C.MS, '11-local-ceiling', 'k6_loop', 'oracle_plain.jsonl')
        self.S = C.fp.Status()
        n = 0
        for f in sorted(glob.glob(os.path.join(HERE, 'data', 'oracle_plain*.jsonl')) +
                        glob.glob(os.path.join(HERE, 'data', 'oracle_plain*.jsonl.gz'))):
            for l in (gzip.open(f, 'rt') if f.endswith('.gz') else open(f)):
                r = json.loads(l)
                if r['result'] == 'UNSAT':
                    for t in itertools.product(*[C.lumped_choices(a) for a in r['alpha']]):
                        self.S.st[C.fp.lkey(tuple(r['dirs']), t)] = 'UNSAT'
                elif all(a[0] == a[1] or tuple(a) == (6, 21) for a in r['alpha']):
                    k = C.fp.lkey(tuple(r['dirs']), tuple(C.GA.sym_of(tuple(a)) for a in r['alpha']))
                    if self.S.st.get(k) in (None, 'TIMEOUT'):
                        self.S.st[k] = r['result']; n += 1
        C.log(f'plain statuses reloaded ({n} from this milestone)')


def main():
    hours = float(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    tllong = float(sys.argv[3]) if len(sys.argv) > 3 else 1800
    pool = mp.get_context('fork').Pool(2)
    st = State()
    t_end = time.time() + hours * 3600
    rnd = sum(1 for _ in open(ROUNDS)) if os.path.exists(ROUNDS) else 0
    stuck = 0
    while time.time() < t_end:
        if C.disk_mb() < 300:
            C.log('disk below 300 MB: stop'); break
        t0 = time.time()
        lam, cyc, nlive = st.evaluate()
        rec = dict(time=time.strftime('%H:%M:%S'), lam=str(lam), mu=float(lam) / 120,
                   m_real=C.bound_real(float(lam), 1, 0, 0), len=len(cyc), live=nlive, par=2)
        steps = []; seen = set()
        for e in cyc:
            ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
            if (k5, k6) not in seen:
                seen.add((k5, k6)); steps.append((e, ds, t, k5, k6))
        tests = []
        # (A) 6-windows
        jobs = {}
        for e, ds, t, k5, k6 in steps:
            if st.S.st.get(k6) is None and k6 not in jobs:
                jobs[k6] = ('p6', k6, C.canon(ds[1:8]), t, tl / 2)
        for job, r in pool.imap_unordered(work, list(jobs.values())):
            k6 = job[1]; st.S.st[k6] = r['result']; tests.append(('p6', r['result'], r['seconds']))
            if r['result'] == 'UNSAT':
                st.exclude(k6)
            elif r['result'] == 'SAT':
                st.X.apply(dict(dirs=list(job[2]), t=list(job[3]), ctx=7, result='SAT', witness5=r['witness5']))
        steps = [s for s in steps if st.S.st.get(s[4]) != 'UNSAT']
        # (B) 5-windows
        jobs = {}
        for e, ds, t, k5, k6 in steps:
            if st.S.st.get(k5) is None and not st.share_state(k5).get('tested') and k5 not in jobs:
                jobs[k5] = ('p5', k5, tl / 2)
        for job, r in pool.imap_unordered(work, list(jobs.values())):
            k5 = job[1]; st.S.st[k5] = r['result']; tests.append(('p5', r['result'], r['seconds']))
            if r['result'] == 'UNSAT':
                st.exclude(k5)
            elif r['result'] == 'SAT':
                st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
        for s in steps:
            if st.S.st.get(s[3]) == 'UNSAT':
                st.exclude(s[3])
        steps = [s for s in steps if st.S.st.get(s[3]) != 'UNSAT']
        # (C) thresholds
        jobs = {}
        for e, ds, t, k5, k6 in steps:
            need = float(lam) + 4 - 120 * int(st.G['A'][e])
            cur = int(st.G['S5'][e])
            if need <= cur:
                continue
            T = LP.next_T(st.share_state(k5))
            if T is not None and T > cur:
                jobs.setdefault(('5', k5), ('t', k5, T, tl))
                continue
            for ctx in (7, 8):
                c = C.canon(ds[8 - ctx:])
                T = L3.next_level(cur, st.X.get((ctx, c, tuple(t))))
                if T is not None:
                    jobs.setdefault((ctx, c, t), ('c', (ctx, c, tuple(t)), T, tl))
                    break
        for job, r in pool.imap_unordered(work, list(jobs.values())):
            if job[0] == 't':
                tests.append(('t', r['T'], r['result'], r['seconds'])); LP.apply_share(st, job[1], r)
            else:
                tests.append((f"c{r['ctx']}", r['T'], r['result'], r['seconds'])); st.ctx_apply(r)
        # (D) long retries
        if not tests:
            long = []
            for e, ds, t, k5, k6 in steps:
                cur = int(st.G['S5'][e])
                s = st.share_state(k5)
                if ('5', k5) not in st.long_tried and s['fail'] < INF and s['lb'] < s['ub'] and s['fail'] > cur:
                    st.long_tried.add(('5', k5)); long.append(('t', k5, min(s['fail'], s['ub']), tllong))
                else:
                    for ctx in (7, 8):
                        c = C.canon(ds[8 - ctx:])
                        sx = st.X.get((ctx, c, tuple(t)))
                        if (ctx, c, t) not in st.long_tried and cur < sx['fail'] < INF and sx['fail'] <= sx['ub']:
                            st.long_tried.add((ctx, c, t)); long.append(('c', (ctx, c, tuple(t)), sx['fail'], tllong))
                            break
                if len(long) >= 2:
                    break
            for job, r in pool.imap_unordered(work, long):
                if job[0] == 't':
                    tests.append(('T', r['T'], r['result'], r['seconds'])); LP.apply_share(st, job[1], r)
                else:
                    tests.append((f"C{r['ctx']}", r['T'], r['result'], r['seconds'])); st.ctx_apply(r)
        rec.update(tests=tests, n_tests=len(tests), s=round(time.time() - t0, 1),
                   cycle=[[int(st.G['A'][e]), int(st.G['S5'][e])] for e in cyc])
        rec['round'] = rnd; rnd += 1
        C.log(f"round {rnd}: lambda {rec['lam']} = {rec['mu']:.4f} m<={rec['m_real']:.3f} len {rec['len']} "
              f"tests {len(tests)} {tests[:5]} [{rec['s']}s]")
        with open(ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        stuck = 0 if tests else stuck + 1
        if stuck >= 2:
            C.log('stuck: no test possible on the minimum cycle'); break
    pool.close()


if __name__ == '__main__':
    main()
