"""loop.py with the solver calls of a round run on 2 worker processes (same tests, same files).

Per round, on the distinct windows of Howard's minimum cycle: (A) plain 6-window tests, (B) plain
5-window tests, (C) share thresholds at the next level, each phase in parallel; then, if the round
could test nothing, long retries of timed-out levels (two at a time).
usage: nice -n 10 python loop2.py HOURS [TL] [TLLONG]
"""
import sys, os, json, time
import multiprocessing as mp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def w_plain(args):
    import solvers as SV
    k, tl = args
    return k, SV.plain(k, tl=tl)


def w_thr(args):
    import solvers as SV
    k, T, tl = args
    return k, SV.share_thr(k, T, tl=tl)


def main():
    hours = float(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 60
    tllong = float(sys.argv[3]) if len(sys.argv) > 3 else 900
    pool = mp.get_context('fork').Pool(2)
    import comb as C
    import loop as LP
    st = LP.State()
    t_end = time.time() + hours * 3600
    rnd = sum(1 for _ in open(LP.ROUNDS)) if os.path.exists(LP.ROUNDS) else 0
    stuck = 0
    while time.time() < t_end:
        t0 = time.time()
        lam, cyc, nlive = st.evaluate()
        rec = dict(time=time.strftime('%H:%M:%S'), lam=str(lam), mu=float(lam) / 120,
                   m_real=C.bound_real(float(lam), 1, 0, 0), len=len(cyc), live=nlive, par=2)
        pairs = []; seen = set()
        for e in cyc:
            ds, t, k5, k6 = C.step_windows(int(st.G['G'][e]), st.Pr)
            if (k5, k6) not in seen:
                seen.add((k5, k6)); pairs.append((e, k5, k6))
        tests = []
        # (A) plain 6-windows
        todo = sorted({k6 for e, k5, k6 in pairs if st.S.st.get(k6) is None})
        for k, r in pool.imap_unordered(w_plain, [(k, tl / 2) for k in todo]):
            st.S.st[k] = r['result']; tests.append(('p6', r['result'], r['seconds']))
            if r['result'] == 'UNSAT':
                st.exclude(k)
        pairs = [(e, k5, k6) for e, k5, k6 in pairs if st.S.st.get(k6) != 'UNSAT']
        # (B) plain 5-windows
        todo = sorted({k5 for e, k5, k6 in pairs if st.S.st.get(k5) is None and not st.share_state(k5).get('tested')})
        for k, r in pool.imap_unordered(w_plain, [(k, tl / 2) for k in todo]):
            st.S.st[k] = r['result']; tests.append(('p5', r['result'], r['seconds']))
            if r['result'] == 'UNSAT':
                st.exclude(k)
            elif r['result'] == 'SAT':
                st.O.apply(dict(dirs=r['dirs'], alpha=r['alpha'], kind='plain', result='SAT', witness=r['witness']))
        for e, k5, k6 in pairs:
            if st.S.st.get(k5) == 'UNSAT':
                st.exclude(k5)
        pairs = [(e, k5, k6) for e, k5, k6 in pairs if st.S.st.get(k5) != 'UNSAT']
        # (C) thresholds
        jobs = {}
        for e, k5, k6 in pairs:
            need = float(lam) + 4 - 120 * int(st.G['A'][e])
            if need <= st.G['S5'][e] or k5 in jobs:
                continue
            T = LP.next_T(st.share_state(k5))
            if T is not None:
                jobs[k5] = T
        for k, r in pool.imap_unordered(w_thr, [(k, T, tl) for k, T in jobs.items()]):
            tests.append(('t', r['T'], r['result'], r['seconds']))
            LP.apply_share(st, k, r)
        if not tests:
            long = []
            for e, k5, k6 in pairs:
                s = st.share_state(k5)
                if k5 in st.long_tried or s['fail'] >= LP.INF or s['lb'] >= s['ub']:
                    continue
                st.long_tried.add(k5); long.append((k5, min(s['fail'], s['ub']), tllong))
                if len(long) == 2:
                    break
            for k, r in pool.imap_unordered(w_thr, long):
                tests.append(('T', r['T'], r['result'], r['seconds']))
                LP.apply_share(st, k, r)
        rec.update(tests=tests, n_tests=len(tests), s=round(time.time() - t0, 1),
                   cycle=[dict(A=int(st.G['A'][e]), S5=int(st.G['S5'][e])) for e in cyc])
        rec['round'] = rnd; rnd += 1
        C.log(f"round {rnd}: lambda {rec['lam']} = {rec['mu']:.4f} m<={rec['m_real']:.3f} len {rec['len']} "
              f"tests {len(tests)} {tests[:6]} [{rec['s']}s]")
        with open(LP.ROUNDS, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        stuck = 0 if tests else stuck + 1
        if stuck >= 2:
            C.log('stuck: no test possible on the minimum cycle'); break
    pool.close()


if __name__ == '__main__':
    main()
