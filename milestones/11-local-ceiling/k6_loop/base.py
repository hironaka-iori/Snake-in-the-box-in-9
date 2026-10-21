"""Upper bound on the base exclusions (those baked into the k5 pickle) that a k6 certificate set needs.

The lifted graph only holds k5 edges that survived the radius-4 oracle cache at pickle time, so
minimal.py counts only the exclusions acting inside it.  Here every candidate k5 edge of the L7 k5 K5
automaton is enumerated; for one that is absent from the pickle and blocked by known-UNSAT windows,
each k6 lift (u, a0) -> (v, a[0]) is checked against the potential of the chosen lambda:
  * both ends in the lifted graph and slack q*w - p + pi[src] - pi[dst] >= 0: harmless;
  * otherwise (negative slack, or an end outside the graph): conservatively needs a blocker.
A greedy hitting set over those blocker sets gives the base count (an upper bound: an end outside
the graph may well be harmless).
usage: base.py A|B LAMBDA   (LAMBDA = p/q in edge-weight units, e.g. 4 for A)
"""
import sys, os, json, itertools
sys.dont_write_bytecode = True
from fractions import Fraction as Fr
import numpy as np
import k6loop as K
from refine import Automaton
from minimal import potential


def main():
    var, lam = sys.argv[1], Fr(sys.argv[2])
    p, q = lam.numerator, lam.denominator
    G = K.build(); P = K.Plain()
    import pickle
    d = pickle.load(open(K.PKL, 'rb')); inv = d['inv']
    present = set(zip(d['U'].tolist(), d['V'].tolist(), d['W'].tolist()))
    # node numbering of k6loop.build
    a0s = {}
    for e in range(len(d['U'])):
        a0s.setdefault(int(d['V'][e]), set()).add(inv[int(d['U'][e])][1][0])
    nodes = {}
    for e in range(len(d['U'])):
        u, v = int(d['U'][e]), int(d['V'][e]); ua = inv[u][1]
        nodes.setdefault((v, ua[0]), len(nodes))
        for a0 in a0s.get(u, ()):
            nodes.setdefault((u, a0), len(nodes))
    del d
    unit = 1 if var == 'A' else K.UNIT
    if var == 'A':
        T5 = np.zeros(len(G['keys5']), np.int64)
    else:
        rs, O = K.share_oracle()
        T5 = np.array([O.st[k]['lb'] if k in O.st else 0 for k in G['keys5']], np.int64)
    b5, b6 = K.masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    W = unit * G['S'].astype(np.int64) + T5[G['K5']]
    pi, _ = potential(G['n6'], G['U'][keep], G['V'][keep], q * W[keep] - p)
    lb5 = {}
    if var == 'B':
        lb5 = {k: O.st[k]['lb'] for k in O.st}
    A = Automaton(7, 5, 5)
    need = []; harmless = 0; absent_unblocked = 0
    for (c, a), u in A.sid.items():
        for ds_ext, nc in A.dtrans[c]:
            for s in A.sym:
                al = a + (s,)
                v = A.sid[(nc, al[1:])]
                if (u, v, s) in present:
                    continue
                ws = A.windows(ds_ext, al)
                bl = [x for x in ws if P.st.get(x) == 'UNSAT']
                if not bl:
                    absent_unblocked += 1; continue
                w = unit * s + lb5.get(ws[3], 0)
                bad = False
                lifts = [a0 for a0 in range(1, 7) if (u, a0) in nodes] or [None]
                for a0 in lifts:
                    src = nodes.get((u, a0)); dst = nodes.get((v, a[0]))
                    if src is None or dst is None or q * w - p + pi[src] - pi[dst] < 0:
                        bad = True; break
                if bad:
                    need.append(frozenset(bl))
                else:
                    harmless += 1
    # greedy hitting set, preferring keys that hit many sets, then fewer centres
    sets = list(set(need)); chosen = set()
    from collections import Counter
    while sets:
        cnt = Counter(x for st in sets for x in st)
        x = max(cnt, key=lambda y: (cnt[y], -len(y[1])))
        chosen.add(x); sets = [st for st in sets if x not in st]
    by = Counter(len(k[1]) for k in chosen)
    out = dict(variant=var, lam=str(lam), blocked_absent_edges=len(need) + harmless, harmless=harmless,
               needing_blocker=len(need), absent_unblocked=absent_unblocked, base_keys=len(chosen),
               base_by_centres=dict(by))
    print(json.dumps(out))
    json.dump(dict(out, keys=[[list(k[0]), [list(x) for x in k[1]]] for k in sorted(chosen)]),
              open(os.path.join(K.HERE, f'base_{var}.json'), 'w'))


if __name__ == '__main__':
    main()
