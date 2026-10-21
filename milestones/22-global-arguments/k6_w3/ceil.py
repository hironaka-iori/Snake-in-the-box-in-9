"""Ceiling search for 'k6 + w_3': the k6 automaton (plain 5- and 6-window exclusions of the
alpha route) with 5-window w_3 charges T5 as edge weights.

Each round: weights on live edges (keys not plain-UNSAT, directly or via a sub-window)
    T5 = ub (exact charge of a SAT witness)            if the 5-window has a witness,
         max(lb, F) + PEN                              otherwise (lb: proved threshold or DP floor);
Howard's minimum cycle; then on that cycle
    6-windows of unknown plain status: plain solve (radius 4, no symmetry breaking; UNSAT removes the edge);
    5-windows without a witness: exact-minimum search (w3survey.search: plain solve, then incremental
        bisection on the w_3 cap, symmetry breaking on) for at most KEYSEC seconds.
A cycle all of whose 5-windows carry witnesses and whose 6-windows are plain-SAT is a rigorous
ceiling for this charge family: no certificate set of 5-window w_3 thresholds plus k <= 6 plain
exclusions can prove a larger mean on it.  The minimum over F = guess is a what-if, not rigorous.
Every round is appended to data/rounds_<tag>.jsonl.
usage: ceil.py F PEN MINUTES [KEYSEC] [TAG] [LONGSEC]
On a witnessed cycle, each of its unsettled 5-window keys gets one long search (LONGSEC) to
lower its witness; the loop then continues until every key of the minimum witnessed cycle is
settled or descended (stop), or the time budget ends.
"""
import sys, os, json, time
from fractions import Fraction as Fr
from k6w3lib import *
import refine_w3 as R


def setup():
    G = build(); P = Plain()
    k6loop.OPLAIN = os.path.join(DATA, 'plain_k6w3.jsonl')    # our new plain calls
    if os.path.exists(k6loop.OPLAIN):
        for l in open(k6loop.OPLAIN):
            r = json.loads(l)
            P.put(k6loop.rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])), r['result'], 'here')
    O = load_w3(); sub = R.Sub()
    return G, P, O, sub


def min_cycle(G, P, O, sub, F, pen):
    b5, b6 = masks(G, P)
    lb, ub = arrays5(G, O, sub)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    T5 = np.where(ub < INF, ub, np.maximum(lb, F) + pen)
    w = T5[G['K5'][idx]]
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    ce = [int(idx[e]) for e in cyc]
    real = [int(np.where(ub < INF, ub, np.maximum(lb, F))[G['K5'][e]]) for e in ce]
    lam = Fr(sum(real), len(ce))
    k5 = [G['keys5'][G['K5'][e]] for e in ce]; k6 = [G['keys6'][G['K6'][e]] for e in ce]
    wit = all(ub[G['K5'][e]] < INF for e in ce) and all(P.st.get(k) == 'SAT' for k in k6)
    return dict(lam=lam, edges=ce, k5=k5, k6=k6, T5=real, lb=[int(lb[G['K5'][e]]) for e in ce],
                witnessed=wit, live=len(idx))


def descend(k, O, sec, steps=(60, 30, 15, 8)):
    """Witness descent: incremental threshold tests just below the current ub (ub - step), keeping
    every SAT witness; a step is abandoned on UNSAT / TIMEOUT.  Logged like w3survey.search."""
    ds, al = k
    w = w3enc.window_from_dirs(list(ds)); nc = len(w) - 2
    s = O.get(k)
    enc = survey.IncW3(w, survey.alpha_arg(al), 4, s['ub'])
    root = enc.root_outputs
    t_end = time.time() + sec
    base = dict(dirs=list(ds), alpha=[list(a) for a in al], kind='descend')
    with survey.Cadical153(bootstrap_with=enc.clauses) as sv:
        for step in steps:
            while time.time() < t_end:
                s = O.get(k)
                T = s['ub'] - step + 1                 # sum <= ub - step
                if T <= s['lb'] or (s['fail'] is not None and T >= s['fail']):
                    break
                idx = T - 168 * nc
                if idx < 1 or idx >= len(root):
                    break
                st, sel, cuts, sec_ = survey.solve_assume(sv, enc, [-root[idx]], min(120, t_end - time.time()))
                wv = w3enc.window_charge(w, sel) if sel else None
                O.log(dict(base, T=T, result=st, witness=wv, seconds=round(sec_, 1), cuts=cuts))
                if st != 'SAT':
                    break


def main():
    F, pen, minutes = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    keysec = float(sys.argv[4]) if len(sys.argv) > 4 else 60
    tag = sys.argv[5] if len(sys.argv) > 5 else f'F{F}p{pen}'
    out = os.path.join(DATA, f'rounds_{tag}.jsonl')
    G, P, O, sub = setup()
    t_end = time.time() + 60 * minutes
    best = None
    rnd = 0
    descended = set()
    longsec = float(sys.argv[6]) if len(sys.argv) > 6 else 600
    while True:
        c = min_cycle(G, P, O, sub, F, pen)
        lam = c['lam']
        rec = dict(round=rnd, time=time.strftime('%H:%M:%S'), F=F, pen=pen, lam=str(lam), mu=float(lam) / 5,
                   m=round(mbound(float(lam) / 5), 3), len=len(c['edges']), witnessed=c['witnessed'],
                   live=c['live'], rss=round(rss_mb()),
                   cycle=[[keystr(a), t, l, keystr(b), P.st.get(b)] for a, b, t, l in zip(c['k5'], c['k6'], c['T5'], c['lb'])])
        print(json.dumps({k: v for k, v in rec.items() if k != 'cycle'}), flush=True)
        for row in rec['cycle']:
            print('    ', row, flush=True)
        with open(out, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if c['witnessed']:
            best = lam if best is None or lam < best else best
            print('WITNESSED cycle: ceiling', lam, mbound(float(lam) / 5), flush=True)
            # lower it: long exact-minimum searches on its keys not yet settled (once per key)
            todo = [k for k in dict.fromkeys(c['k5']) if k not in descended and O.get(k)['lb'] < O.get(k)['ub']]
            if not todo or time.time() > t_end:
                print('stop: witnessed cycle with every key settled or descended; best', best, flush=True)
                break
            for k in todo:
                descended.add(k)
                s = O.get(k)
                descend(k, O, longsec)
                s = O.get(k)
                print(f'   descend {keystr(k)}: lb {s["lb"]} ub {s["ub"]} fail {s["fail"]}', flush=True)
            rnd += 1
            continue
        if time.time() > t_end:
            break
        seen = set()
        for k5, k6 in zip(c['k5'], c['k6']):
            if time.time() > t_end:
                break
            if k6 not in P.st and k6 not in seen:
                seen.add(k6)
                r = P.test(k6, 60)
                print(f'   6w plain {keystr(k6)}: {r["result"]} {r["seconds"]}s', flush=True)
                if r['result'] == 'UNSAT':
                    continue
            if P.blocked(k6) or k5 in seen:
                continue
            seen.add(k5)
            s = O.get(k5)
            if s['ub'] is None and not s['excl']:
                lbf = max(s['lb'], sub.floor5(k5))
                survey.search(k5, O, min(keysec, 60), keysec, lbf, verbose=False)
                s = O.get(k5)
                print(f'   5w w3 {keystr(k5)}: lb {s["lb"]} ub {s["ub"]} excl {s["excl"]} fail {s["fail"]} rss {rss_mb():.0f}', flush=True)
                if s['excl']:
                    P.put(k5, 'UNSAT', 'w3excl')
        rnd += 1


if __name__ == '__main__':
    main()
