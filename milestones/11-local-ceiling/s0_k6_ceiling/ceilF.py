"""Ceiling search on the FULL radius-4 L7 k6 automaton: k5 share weights + k6 plain exclusions.

Weight of a k6 edge = 120 sym + T5(key5 of its k5 edge), as in the share loop, with the 6-windows proved
plain-UNSAT removed.  hi: T5 = best 5-window witness; a 5-window without a witness gets max(G, proved lb), G = GUESS
(search heuristic only).  Each round takes the minimum cycle and tests its untested windows: 5-windows by a plain solve
and a threshold test at min(ub, 108) (exactly the share loop's first visit), 6-windows by a plain solve.  When
the minimum cycle has no untested window, every window on it carries a witness: its mean is a rigorous ceiling
for k5-share certificates plus k6 plain exclusions on this automaton (and the lowest one found, given G).
With a penalty P (4th argument) every window without a witness adds P to the search weight only, which
steers the search to cycles that can be completed (a rigorous ceiling sooner).
usage: ceilF.py G rounds [tl] [P]"""
import sys, os, json, time
sys.dont_write_bytecode = True
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
from fractions import Fraction as Fr
import numpy as np
from k6lib import key
import refine_share as rs
from refine import Automaton, howard, prune
from ceil6 import Oracle6, test6, INF
HERE = os.path.dirname(os.path.abspath(__file__))
OR5X = os.path.join(HERE, 'oracle5_extra.jsonl')
HOPELESS = set()

def load_hopeless():
    for fn in (OR5X, os.path.join(HERE, 'oracle6.jsonl')):
        if os.path.exists(fn):
            for l in open(fn):
                r = json.loads(l)
                if r['kind'] == 'plain' and r['result'] == 'TIMEOUT':
                    HOPELESS.add(key(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])))

def build_full():
    n, U, V, S, KI, keys = rs.load_compact(rs.DEFAULT_PKL)
    O5 = rs.ShareOracle()
    rs.ORACLE = OR5X                       # new 5-window calls go to this directory
    if os.path.exists(OR5X):
        for l in open(OR5X):
            O5.apply(json.loads(l))
    ex5 = np.array([O5.st[k]['excl'] if k in O5.st else False for k in keys], bool)
    keep = ~ex5[KI]
    U, V, S, KI = U[keep], V[keep], S[keep], KI[keep]
    m = prune(n, U, V); U, V, S, KI = U[m], V[m], S[m], KI[m]
    A = Automaton(7, 5, 5); inv = {u: s for s, u in A.sid.items()}
    rng = lambda s: (s, s) if s <= 5 else (6, 21)
    a0s = {}
    for e in range(len(U)):
        a0s.setdefault(int(V[e]), set()).add(inv[int(U[e])][1][0])
    nodes = {}; U6, V6, E5, K6 = [], [], [], []; kid = {}; keys6 = []
    for e in range(len(U)):
        u, v = int(U[e]), int(V[e]); vd, va = inv[v]; ua = inv[u][1]
        dst = nodes.setdefault((v, ua[0]), len(nodes))
        for a0 in a0s.get(u, ()):
            k6 = key(vd, tuple(rng(s) for s in (a0,) + ua + (va[-1],)))
            if k6 not in kid:
                kid[k6] = len(keys6); keys6.append(k6)
            U6.append(nodes.setdefault((u, a0), len(nodes))); V6.append(dst); E5.append(e); K6.append(kid[k6])
    return dict(n6=len(nodes), U6=np.array(U6, np.int32), V6=np.array(V6, np.int32), E5=np.array(E5, np.int32),
                K6=np.array(K6, np.int32), keys6=keys6, S=S, KI=KI, keys5=keys, O5=O5)

def evaluate(G, O5, O6, guess, pen=0):
    k5, k6 = G['keys5'], G['keys6']
    ex5 = np.array([O5.st[k]['excl'] if k in O5.st else False for k in k5], bool)
    ub5 = np.array([O5.st[k]['ub'] if k in O5.st else INF for k in k5], np.int64)
    lb5 = np.array([O5.st[k]['lb'] if k in O5.st else 0 for k in k5], np.int64)
    t5 = ub5 < INF                         # a ceiling needs a witness for every 5-window
    ex6 = np.array([O6.st[k]['excl'] if k in O6.st else False for k in k6], bool)
    t6 = np.array([O6.st[k]['tested'] if k in O6.st else False for k in k6], bool)
    keep = ~ex6[G['K6']] & ~ex5[G['KI'][G['E5']]]
    if pen:   # completion search: drop windows whose plain solve timed out (they can never get a witness here)
        h5 = np.array([k in HOPELESS for k in k5], bool); h6 = np.array([k in HOPELESS for k in k6], bool)
        keep &= ~h6[G['K6']] & ~h5[G['KI'][G['E5']]]
    m = prune(G['n6'], G['U6'][keep], G['V6'][keep]); idx = np.nonzero(keep)[0][m]
    ki = G['KI'][G['E5'][idx]]
    T5 = np.where(ub5[ki] < INF, ub5[ki], np.maximum(guess, lb5[ki]))
    w = 120 * G['S'][G['E5'][idx]].astype(np.int64) + T5
    # search penalty for windows without a witness (0 = plain guess search); the reported mean excludes it
    ws_ = w + pen * ((~t5[ki]).astype(np.int64) + (~t6[G['K6'][idx]]).astype(np.int64))
    _, cyc = howard(G['n6'], G['U6'][idx], G['V6'][idx], ws_)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    c5 = [int(ki[e]) for e in cyc]; c6 = [int(G['K6'][idx[e]]) for e in cyc]
    return dict(lam=lam, mu=float(lam) / 120, m_le=9171 / (float(lam) / 120 + 35), len=len(cyc),
                syms=[int(G['S'][G['E5'][idx[e]]]) for e in cyc], T5=[int(T5[e]) for e in cyc],
                todo5=sorted({i for i in c5 if not t5[i]}), todo6=sorted({i for i in c6 if not t6[i]}),
                lb5=[int(O5.st[k5[i]]['lb']) if k5[i] in O5.st else 0 for i in c5],
                keys5=[k5[i] for i in c5], keys6=[k6[i] for i in c6], edges=int(len(idx)))

def main():
    guess, rounds = int(sys.argv[1]), int(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 60
    pen = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    t = time.time(); G = build_full(); O5 = G['O5']; O6 = Oracle6(); load_hopeless()
    print(f'full k6 automaton: {G["n6"]} states, {len(G["U6"])} edges, {len(G["keys6"])} 6-keys [{time.time()-t:.0f}s]', flush=True)
    for rnd in range(rounds):
        t = time.time(); ev = evaluate(G, O5, O6, guess, pen)
        rec = dict(guess=guess, pen=pen, round=rnd, time=time.strftime('%H:%M:%S'), lam=str(ev['lam']), mu=round(ev['mu'], 5),
                   m_le=round(ev['m_le'], 3), len=ev['len'], syms=ev['syms'], T5=ev['T5'], lb5=ev['lb5'],
                   todo5=len(ev['todo5']), todo6=len(ev['todo6']), edges=ev['edges'], eval_s=round(time.time() - t, 1))
        if not ev['todo5'] and not ev['todo6']:
            rec['rigorous_ceiling'] = True
            rec['keys5'] = [[list(k[0]), [list(a) for a in k[1]]] for k in ev['keys5']]
            rec['keys6'] = [[list(k[0]), [list(a) for a in k[1]]] for k in ev['keys6']]
        print(json.dumps({k: v for k, v in rec.items() if k not in ('keys5', 'keys6')}), flush=True)
        with open(os.path.join(HERE, f'rounds_F{guess}_p{pen}.jsonl'), 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if rec.get('rigorous_ceiling'):
            print('minimum cycle fully tested: rigorous ceiling', flush=True); break
        for i in ev['todo6']:                       # cheap first: 6-window plain solves
            r = test6(G['keys6'][i], 'plain', None, tl); O6.apply(r)
            if r['result'] == 'TIMEOUT': HOPELESS.add(G['keys6'][i])
            print(f"   k6 plain {r['dirs']} {[a[0] for a in r['alpha']]}: {r['result']} w={r['witness']} {r['seconds']}s", flush=True)
        for i in ev['todo5']:
            k = G['keys5'][i]
            r = rs.run_test(k, 'plain', None, tl / 2); O5.apply(r)
            msg = f"   k5 plain {k[0]} {[x[0] for x in k[1]]}: {r['result']} w={r['witness']} {r['seconds']}s"
            if r['result'] == 'TIMEOUT':
                HOPELESS.add(k); print(msg, '(no witness; window kept at the guess)', flush=True)
            T = O5.next_T(k)
            if T is not None:
                r = rs.run_test(k, 'thr', T, tl); O5.apply(r)
                msg += f" | T={T}: {r['result']} w={r['witness']} {r['seconds']}s"
            print(msg, flush=True)

if __name__ == '__main__':
    main()
