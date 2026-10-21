"""Per-shape incremental sweeps over the live 6-window keys of the k6 automaton (as ../w3_survey/sweep_w3.py).

One CaDiCaL instance per 6-window direction shape (21 shapes): wincert.Encoding with alpha free plus,
per centre, the two-sided totalizer over its opposite corners (sweep_w3.AlphaInc); a key's alpha ranges
are assumptions.  An UNSAT under assumptions implies UNSAT of the key's static CNF (same base, the
alpha / cap clauses of the static CNF are implied by the assumptions).

  plain:  no charge totalizer, no symmetry breaking; result = plain status of the 6-window
          (logged to data/plain_loop.jsonl, kind 'plain', exactly like k6loop.Plain.test).
  T=<n>:  charge totalizer (symmetry breaking on) and the assumption  sum c <= T-1; UNSAT = lb T.
          Logged to data/w3_loop_oracle.jsonl (kind 'sweep6').  Only plain-SAT keys with W6 < T.

Keys are taken in order of increasing W6 among the live 6-keys with W6 < MAXW, per shape.
usage: sweep6.py plain|T MINUTES [MAXW] [TL]
"""
import sys, os, json, time
ME = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, ME)
import k6w3loop as L
from k6w3loop import *
from collections import defaultdict, Counter
from sweep_w3 import AlphaInc


def main():
    mode = sys.argv[1]; minutes = float(sys.argv[2])
    maxw = int(sys.argv[3]) if len(sys.argv) > 3 else 1700
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else (10 if mode == 'plain' else 20)
    t_end = time.time() + 60 * minutes
    G, P, O, sub = setup(); Tb = Tables(G, sub)
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    W6, lb5, ub6 = Tb.weights(G, O)
    ks = np.unique(G['K6'][idx])
    T = None if mode == 'plain' else int(mode)
    lim = maxw if T is None else min(maxw, T)
    todo = defaultdict(list)
    for j in ks:
        k = G['keys6'][j]
        if W6[j] >= lim:
            continue
        if T is None:
            if P.st.get(k) is None:
                todo[k[0]].append((int(W6[j]), k))
        else:
            s = O.get(k)
            if P.st.get(k) == 'SAT' and (s['ub'] is None or s['ub'] >= T) and (s['fail'] is None or s['fail'] > T):
                todo[k[0]].append((int(W6[j]), k))
    tot = sum(len(v) for v in todo.values())
    print(f'sweep6 {mode}: {tot} keys in {len(todo)} shapes (W6 < {lim})', flush=True)
    stats = Counter()
    for ds in sorted(todo, key=lambda d: min(todo[d])[0]):
        if time.time() > t_end:
            break
        survey.wait_mem()
        t0 = time.time()
        w = w3enc.window_from_dirs(list(ds))
        enc = AlphaInc(w, None, 4, None if T is None else T + 1, sym=(T is not None))
        print(f' shape {ds}: {len(todo[ds])} keys, {enc.nv} vars {len(enc.clauses)} clauses, build {time.time()-t0:.0f}s rss {rss_mb():.0f}', flush=True)
        st_shape = Counter()
        with survey.Cadical153(bootstrap_with=enc.clauses) as sv:
            for wv0, k in sorted(todo[ds]):
                if time.time() > t_end:
                    break
                ass = []
                for i, (lo, hi) in enumerate(k[1]):
                    o = enc.atot[i]
                    if lo >= 1:
                        ass.append(o[lo])
                    if hi < 21:
                        ass.append(-o[hi + 1])
                if T is not None:
                    ass.append(-enc.root_outputs[T - w3enc.BASE * 6])
                st, sel, cuts, sec = survey.solve_assume(sv, enc, ass, tl)
                if T is None:
                    r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='plain', k=6, result=st,
                             witness=None, w3=w3enc.window_charge(w, sel) if sel else None, cuts=cuts,
                             seconds=round(sec, 3), src='sweep6')
                    with open(L.OPL, 'a') as f:
                        f.write(json.dumps(r) + '\n')
                    P.put(k, st, 'here')
                    if sel:     # a plain model is a witness of the 6-window charge
                        O.log(dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], T=None, result='SAT',
                                   witness=r['w3'], seconds=0, cuts=0, kind='plainwit'))
                else:
                    wv = w3enc.window_charge(w, sel) if sel else None
                    O.log(dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], T=T, result=st, witness=wv,
                               seconds=round(sec, 2), cuts=cuts, kind='sweep6'))
                stats[st] += 1; st_shape[st] += 1
        print(f'   done {ds}: {dict(st_shape)} [{time.time()-t0:.0f}s] total {dict(stats)}', flush=True)
    print('sweep6 finished', dict(stats), flush=True)


if __name__ == '__main__':
    main()
