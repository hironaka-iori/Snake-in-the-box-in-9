"""Rigorous ceiling for the five-centre w_3 automaton: find a cycle whose windows all have SAT
witnesses (then no certificate set of this window family can prove a larger mean on it).

Loop: take the min cycle of the optimistic weights  T5 = ub (witnessed keys) or max(lb, F)
(unwitnessed keys, F = guess); every unwitnessed key on it gets a witness search: threshold
tests at T = F, F + 40, F + 80, ... (SAT -> ub = exact charge of the witness).  When the cycle is
fully witnessed its ub mean is a rigorous ceiling; the loop then tries to lower it by
descending the witnesses of its keys (T = ub).
usage: ceiling_probe.py --minutes 25 [--F 1420] [--tl 60]
"""
import argparse, json, os, sys, time
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import refine_w3 as R
from refine import howard
from eval_w3 import final_m

OUT = os.path.join(HERE, 'data', 'ceiling_probe.jsonl')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--minutes', type=float, default=25)
    ap.add_argument('--F', type=int, default=1420)
    ap.add_argument('--tl', type=float, default=60)
    a = ap.parse_args()
    t_end = time.time() + 60 * a.minutes
    n, U, V, S, KI, keys = R.load_compact()
    sub = R.Sub(); O = R.W3Oracle()
    best = None
    while time.time() < t_end:
        lb = np.array([max(O.st[k]['lb'] if k in O.st else 0, sub.floor5(k)) for k in keys], np.int64)
        ub = np.array([O.st[k]['ub'] if k in O.st else R.INF for k in keys], np.int64)
        T5 = np.where(ub < R.INF, ub, np.maximum(lb, a.F))
        w = T5[KI]
        _, cyc = howard(n, U, V, w)
        lam = Fr(int(w[cyc].sum()), len(cyc))
        ck = sorted(set(int(KI[e]) for e in cyc))
        full = all(ub[i] < R.INF for i in ck)
        rec = dict(time=time.strftime('%H:%M:%S'), lam=str(lam), w3=float(lam) / 60,
                   m=final_m(lam.numerator, lam.denominator, 0), witnessed=full, len=len(cyc),
                   cycle=[[list(keys[KI[e]][0]), [x[0] for x in keys[KI[e]][1]], int(T5[KI[e]]), int(lb[KI[e]])] for e in cyc])
        print(json.dumps({k: v for k, v in rec.items() if k != 'cycle'}), flush=True)
        with open(OUT, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if full:
            if best is None or lam < best:
                best = lam
            # lower the ceiling: descend witnesses not yet proved optimal
            todo = [(keys[i], int(ub[i])) for i in ck if lb[i] < ub[i] and O.get(keys[i])['fail'] > ub[i]]
            if not todo:
                print('converged: the witnessed cycle is exact', flush=True); break
        else:
            todo = []
            for i in ck:
                if ub[i] < R.INF:
                    continue
                s = O.get(keys[i])
                T = max(a.F, int(lb[i]) + 1) if lb[i] < a.F else int(lb[i]) + 40
                if s['fail'] < R.INF:
                    T = max(T, s['fail'] + 40)      # above a hard (timed-out) level SAT is easier
                todo.append((keys[i], T))
        for k, T in todo:
            if time.time() > t_end:
                break
            r = R.run_test(k, T, a.tl, 0); O.apply(r)
            print(f"   T={T} {k[0]} {[x[0] for x in k[1]]}: {r['result']} w={r['witness']} {r['seconds']}s", flush=True)
    if best is not None:
        print('ceiling lambda', best, float(best) / 60, 'm <=', final_m(best.numerator, best.denominator, 0))


if __name__ == '__main__':
    main()
