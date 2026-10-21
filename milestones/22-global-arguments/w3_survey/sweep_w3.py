"""Threshold sweep over the five-centre keys of the alpha automaton, one incremental solver per
direction shape.

For a shape, the CNF is wincert.Encoding with alpha unconstrained, the W3 charge totalizer
(reach 5*REACH) and, per centre, a two-sided totalizer a[j] <-> (#absent opposite corners >= j)
over its 21 corners.  A key (shape, alpha ranges) at threshold T is the assumption set
    a_i[lo_i] (lo_i >= 1),  -a_i[hi_i + 1] (hi_i < 21),  -o[T - 840],
so every test reuses the learnt clauses of the shape.  UNSAT means: the static CNF of the key
(alpha units of wincert + cap T-1, as in refine_w3 / w3enc) is UNSAT as well, since its clauses
are implied by these assumptions over the same base; it is the certificate that would be
regenerated cold.  SAT gives a witness whose exact charge is the ub.

Records go to the same oracle file as refine_w3 (kind 'sweep').
usage: sweep_w3.py --T 1420 --minutes 75 [--tl 8] [--max-floor 1400]
"""
import argparse, json, os, sys, time
from collections import defaultdict
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import w3enc
import w3survey as survey
from w3survey import solve_assume
import refine_w3 as R
from itertools import combinations
from pysat.solvers import Cadical153

REACH = 330


class AlphaInc(w3enc.W3Encoding):
    noUnit = True

    def build(self):
        super().build()
        X, w = self.var, self.window
        self.atot = []
        for ci in range(1, len(w) - 1):
            c = w[ci]
            used = w3enc.path_dirs(w, ci)
            corners = [X[c ^ 1 << a ^ 1 << b] for a, b in combinations(range(9), 2)
                       if a not in used and b not in used]
            self.atot.append(self.totalizer([-x for x in corners], up=True, down=True))
        # build() of W3Encoding built the w3 totalizer first; root_outputs kept

    def assumptions(self, al, T):
        out = []
        for i, (lo, hi) in enumerate(al):
            o = self.atot[i]
            if lo >= 1:
                out.append(o[lo])
            if hi < 21:
                out.append(-o[hi + 1])
        idx = T - w3enc.BASE * len(al)
        out.append(-self.root_outputs[idx])
        return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--T', type=int, default=1420)
    ap.add_argument('--minutes', type=float, default=75)
    ap.add_argument('--tl', type=float, default=8)
    ap.add_argument('--max-floor', type=int, default=10 ** 6)
    a = ap.parse_args()
    t_end = time.time() + a.minutes * 60
    n, U, V, S, KI, keys = R.load_compact()
    sub = R.Sub(); O = R.W3Oracle()
    todo = defaultdict(list)
    for k in keys:
        s = O.get(k)
        fl = sub.floor5(k)
        if max(s['lb'], fl) >= a.T or s['ub'] < a.T or s['fail'] <= a.T or fl > a.max_floor:
            continue
        todo[k[0]].append((fl, k))
    tot = sum(len(v) for v in todo.values())
    print(f'sweep T={a.T}: {tot} keys in {len(todo)} shapes', flush=True)
    stats = defaultdict(int)
    # shapes in order of their lowest floor
    for ds in sorted(todo, key=lambda d: min(todo[d])[0]):
        if time.time() > t_end:
            break
        survey.wait_mem()
        t0 = time.time()
        enc = AlphaInc(w3enc.window_from_dirs(list(ds)), None, 4, 5 * REACH)
        print(f' shape {ds}: {len(todo[ds])} keys, {enc.nv} vars {len(enc.clauses)} clauses, build {time.time()-t0:.0f}s', flush=True)
        with Cadical153(bootstrap_with=enc.clauses) as sv, open(R.ORACLE, 'a') as f:
            for fl, k in sorted(todo[ds]):
                if time.time() > t_end:
                    break
                st, sel, cuts, sec = solve_assume(sv, enc, enc.assumptions(k[1], a.T), a.tl)
                wv = w3enc.window_charge(enc.window, sel) if sel else None
                r = dict(dirs=list(k[0]), alpha=[list(x) for x in k[1]], T=a.T, result=st, witness=wv,
                         cuts=cuts, seconds=round(sec, 2), kind='sweep')
                f.write(json.dumps(r) + '\n'); f.flush()
                stats[st] += 1
        print(f'   done shape {ds}: {dict(stats)} [{time.time()-t0:.0f}s]', flush=True)
    print('sweep finished', dict(stats), flush=True)


if __name__ == '__main__':
    main()
