"""Ceiling of the radius-4 L7 k6 share automaton built on the k5 share loop.

The L7 k6 automaton is the k5 one with one more remembered count: state (v, a0), where v is a k5 state
(7 canonical directions, last 4 counts) and a0 the count before them.  A k5 edge e: v -> w gives the k6 edge
(v, a0) -> (w, v.alpha[0]), whose 6-window key is key(w.dirs, (a0,) + v.alpha + (new,)): the 7 directions of
a 6-centre window are exactly the 7 remembered directions of the target state, so the key is well defined.

Rigorous ceilings (upper bounds on what any certificate set of the given kind can reach on this automaton):
  mode A  weight 120 sym + T5_ub(key5)   (k5 shares as in the loop; T5_ub = best 5-window witness, INF untested)
          minus k6 windows proved plain-UNSAT.
  mode B  weight 144 sym + T6_ub(key6)   (6-window shares; T6_ub = best 6-window witness, INF untested)
A cycle all of whose windows carry witnesses is a periodic pattern that no certificate of that kind can lift.
Each round tests the untested 6-windows of the minimum cycle (plain solve at radius 4; the witness share is
recorded as T6_ub; in mode B also a threshold test to lower T6_ub).
usage: ceil6.py A|B rounds [tl]"""
import sys, os, json, time, pickle
sys.dont_write_bytecode = True
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
from fractions import Fraction as Fr
import numpy as np
from k6lib import wincert, ws, key
import refine_share as rs
from refine import Automaton, howard, prune
HERE = os.path.dirname(os.path.abspath(__file__))
OR6 = os.path.join(HERE, 'oracle6.jsonl')
INF = 10 ** 6
M = 12

def mem_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 1e6

class Oracle6:
    def __init__(self):
        self.st = {}
        if os.path.exists(OR6):
            for l in open(OR6):
                self.apply(json.loads(l))
    def get(self, k):
        return self.st.setdefault(k, dict(excl=False, ub=INF, lb=0, fail=INF, tested=False))
    def apply(self, r):
        k = (tuple(r['dirs']), tuple(tuple(a) for a in r['alpha'])); s = self.get(k); s['tested'] = True
        if r['kind'] == 'plain':
            if r['result'] == 'UNSAT': s['excl'] = True
            elif r['result'] == 'SAT': s['ub'] = min(s['ub'], r['witness'])
        else:
            if r['result'] == 'UNSAT': s['lb'] = max(s['lb'], r['T'])
            elif r['result'] == 'SAT': s['ub'] = min(s['ub'], r['witness'])
            elif r['result'] == 'TIMEOUT': s['fail'] = min(s['fail'], r['T'])

def test6(k, kind, T=None, tl=60.0):
    while mem_gb() < 3.0:
        print('   low memory, pausing', flush=True); time.sleep(60)
    ds, al = k
    w = wincert.window_from_dirs(list(ds)); alpha = ws.alpha_arg(al)
    enc = wincert.Encoding(w, alpha, 4) if kind == 'plain' else ws.ShareEncoding(w, alpha, 4, M, T - 1)
    st, sel, cuts, sec = ws.solve(enc, tl)
    r = dict(dirs=list(ds), alpha=[list(a) for a in al], kind=kind, T=T, result=st, cuts=cuts, seconds=round(sec, 1),
             witness=ws.share_exact(enc, sel, M) if sel else None)
    with open(OR6, 'a') as f:
        f.write(json.dumps(r) + '\n')
    return r

def build():
    n, U, V, S, KI, keys = rs.load_compact(rs.DEFAULT_PKL)
    O5 = rs.ShareOracle()
    ub5 = np.array([O5.st[k]['ub'] if k in O5.st else INF for k in keys], np.int64)
    lb5 = np.array([O5.st[k]['lb'] if k in O5.st else 0 for k in keys], np.int64)
    ex5 = np.array([O5.st[k]['excl'] if k in O5.st else False for k in keys], bool)
    keep = (~ex5[KI]) & (ub5[KI] < INF)
    U, V, S, KI = U[keep], V[keep], S[keep], KI[keep]
    m = prune(n, U, V); U, V, S, KI = U[m], V[m], S[m], KI[m]
    A = Automaton(7, 5, 5); inv = {u: s for s, u in A.sid.items()}
    rng = lambda s: (s, s) if s <= 5 else (6, 21)
    # k6 nodes (v, a0); in-edges to v determine the admissible a0 = alpha[0] of the source
    nodes = {}; E = []
    ins = {}
    for e in range(len(U)):
        ins.setdefault(int(V[e]), set()).add(inv[int(U[e])][1][0])
    for e in range(len(U)):
        u, v = int(U[e]), int(V[e])
        for a0 in ins.get(u, ()):
            src = nodes.setdefault((u, a0), len(nodes)); dst = nodes.setdefault((v, inv[u][1][0]), len(nodes))
            vd, va = inv[v]; ua = inv[u][1]
            al6 = (a0,) + ua + (va[-1],)
            k6 = key(vd, tuple(rng(s) for s in al6))
            E.append((src, dst, e, k6))
    keys6 = sorted({x[3] for x in E}); kid = {k: i for i, k in enumerate(keys6)}
    U6 = np.array([x[0] for x in E], np.int32); V6 = np.array([x[1] for x in E], np.int32)
    E5 = np.array([x[2] for x in E], np.int32); K6 = np.array([kid[x[3]] for x in E], np.int32)
    return dict(n6=len(nodes), U6=U6, V6=V6, E5=E5, K6=K6, keys6=keys6, S=S, KI=KI, keys5=keys,
                ub5=ub5, lb5=lb5)

def evaluate(G, O6, mode):
    keys6 = G['keys6']
    ex6 = np.array([O6.st[k]['excl'] if k in O6.st else False for k in keys6], bool)
    ub6 = np.array([O6.st[k]['ub'] if k in O6.st else INF for k in keys6], np.int64)
    tested = np.array([O6.st[k]['tested'] if k in O6.st else False for k in keys6], bool)
    keep = ~ex6[G['K6']]
    m = prune(G['n6'], G['U6'][keep], G['V6'][keep]); idx = np.nonzero(keep)[0][m]
    sym = G['S'][G['E5'][idx]].astype(np.int64)
    if mode == 'A':
        w = 120 * sym + G['ub5'][G['KI'][G['E5'][idx]]]; unit = 120
    else:
        u6 = ub6[G['K6'][idx]]
        # untested 6-windows: INF (rigorous); tie-break by 6/5 of the 5-window witness so the search is guided
        soft = np.where(u6 < INF, u6, 10 ** 5 + (6 * G['ub5'][G['KI'][G['E5'][idx]]]) // 5)
        w = 144 * sym + soft; unit = 144
    _, cyc = howard(G['n6'], G['U6'][idx], G['V6'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    ks = [int(G['K6'][idx[e]]) for e in cyc]
    return dict(lam=lam, mu=float(lam) / unit, m_le=9171 / (float(lam) / unit + 35), syms=[int(x) for x in sym[cyc]],
                keys6=ks, untested=[i for i in ks if not tested[i]], finite=bool(w[cyc].max() < 10 ** 5),
                edges=int(len(idx)), T5=[int(G['ub5'][G['KI'][G['E5'][idx[e]]]]) for e in cyc],
                T6=[int(ub6[i]) for i in ks])

def main():
    mode, rounds = sys.argv[1], int(sys.argv[2]); tl = float(sys.argv[3]) if len(sys.argv) > 3 else 60
    t = time.time(); G = build()
    print(f'k6 automaton (finite-ub k5 edges only): {G["n6"]} states, {len(G["U6"])} edges, {len(G["keys6"])} 6-keys, '
          f'{time.time()-t:.0f}s', flush=True)
    O6 = Oracle6()
    for rnd in range(rounds):
        ev = evaluate(G, O6, mode)
        rec = dict(mode=mode, round=rnd, time=time.strftime('%H:%M:%S'), lam=str(ev['lam']), mu=round(ev['mu'], 5),
                   m_le=round(ev['m_le'], 3), syms=ev['syms'], T5=ev['T5'], T6=ev['T6'], finite=ev['finite'],
                   untested=len(set(ev['untested'])), edges=ev['edges'])
        print(json.dumps(rec), flush=True)
        with open(os.path.join(HERE, f'rounds_{mode}.jsonl'), 'a') as f:
            f.write(json.dumps(rec) + '\n')
        todo = sorted(set(ev['untested']))
        if mode == 'B' and not todo:       # lower the witnesses of the binding cycle by threshold tests
            for i in sorted(set(ev['keys6'])):
                s = O6.get(G['keys6'][i])
                if s['excl'] or s['lb'] >= s['ub'] or s['fail'] <= s['ub']: continue
                T = s['ub'] if s['fail'] == INF else None
                if T is None: continue
                todo.append(('thr', i, T))
        if not todo:
            print('cycle fully tested: rigorous ceiling', flush=True); break
        for it in todo:
            if isinstance(it, tuple):
                _, i, T = it; r = test6(G['keys6'][i], 'thr', T, tl)
            else:
                i = it; r = test6(G['keys6'][i], 'plain', None, tl)
            O6.apply(r)
            print(f"   {r['kind']} T={r['T']} {r['dirs']} {[a[0] for a in r['alpha']]}: {r['result']} w={r['witness']} {r['seconds']}s", flush=True)

if __name__ == '__main__':
    main()
