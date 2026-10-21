"""Refinement loops on the radius-4 L7 k6 K5 direction automaton (two variants).

Automaton.  A state is (7 canonical directions, last 5 counts), counts in 1..5 and 6 = 6..21.  It is
built by lifting the radius-4 L7 k5 automaton (the 240,729-edge pickle of the share loop, whose edges
already avoid every radius-4 window the oracle cache knew to be UNSAT): a k5 edge e: v -> w becomes
(v, a0) -> (w, v.alpha[0]).  Every k6 edge carries two keys:
    key5 = the 5-centre window ending at the new vertex (that of the k5 edge),
    key6 = the 6-centre window ending at the new vertex (the target state's 7 directions, 6 counts).
The key5 of every edge INTO a node (v, a0) is the same (it is the left 5-sub-window of key6), so an
UNSAT 5-window removes whole nodes; UNSAT 6-windows remove single edges.

Variant A (plain):  weight sym; edges with key5 or key6 plain-UNSAT at radius 4 are removed.
    Each round takes the minimum-mean cycle (Howard) and tests every untested window on it, the
    5-window first (a hit removes more), then the 6-window.  Converged when every window on the
    minimum cycle is SAT (or timed out): the mean is then the ceiling of this abstraction.
Variant B (share):  weight 120 sym + T5_lb(key5) (rigorous; 0 untested), same exclusions.  Each round
    tests the lo cycle like ../s0_share_loop/refine_share.py (plain, then the threshold ladder at 108,
    150, ...) for 5-windows, and plain solves for 6-windows.

Resumable: every solver call is appended to oracle_plain.jsonl / oracle_share.jsonl, every round to
rounds_A.jsonl / rounds_B.jsonl.
usage: k6loop.py A|B HOURS [TL]     |   k6loop.py evalA | evalB
"""
import sys, os, json, time, pickle
sys.dont_write_bytecode = True
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
from fractions import Fraction as Fr
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
MS = os.path.join(HERE, '..', '..')
sys.path.insert(0, os.path.join(HERE, '..', 's0_share_loop'))
sys.path.insert(0, os.path.join(MS, '10-window-aggregate', 'scripts'))
import wincert, wincert_share as ws
from refine import howard, prune, key as rkey, canon

SCR = os.environ.get('K6SCR', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/k6loop')
PKL = os.environ.get('K5PKL', '/tmp/claude-0/-home-user-Snake-in-the-box-in-9/9d4b5ea1-0097-55fa-8dda-100e9a084d22/scratchpad/agents/e1/aut_L7k5K5r4.pkl')
OPLAIN = os.path.join(HERE, 'oracle_plain.jsonl')
OSHARE = os.path.join(HERE, 'oracle_share.jsonl')
INF = 10 ** 6
UNIT = 120


def bound_m(mu):
    return 9171 / (mu + 35)


def mem_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable'):
            return int(l.split()[1]) / 1e6
    return 99


def disk_mb():
    s = os.statvfs('/'); return s.f_bavail * s.f_frsize / 2 ** 20


def wait_res():
    while mem_gb() < 3.0:
        print(f'   low memory ({mem_gb():.1f} GB), pausing', flush=True); time.sleep(60)
    while disk_mb() < 300:
        print(f'   low disk ({disk_mb():.0f} MB), pausing', flush=True); time.sleep(300)


# ------------------------------------------------------------------ graph
def build():
    npz = os.path.join(SCR, 'k6graph.npz'); kp = os.path.join(SCR, 'k6keys.pkl')
    if os.path.exists(npz) and os.path.exists(kp):
        z = np.load(npz); k5, k6 = pickle.load(open(kp, 'rb'))
        return dict(n6=int(z['n6']), U=z['U'], V=z['V'], S=z['S'], K5=z['K5'], K6=z['K6'], keys5=k5, keys6=k6)
    d = pickle.load(open(PKL, 'rb'))
    U, V, W, inv = d['U'], d['V'], d['W'], d['inv']
    keys5, kid5 = [], {}
    KI = np.empty(len(U), np.int32)
    for e, w in enumerate(d['WIN']):
        k = w[3]
        if k not in kid5:
            kid5[k] = len(keys5); keys5.append(k)
        KI[e] = kid5[k]
    del d
    rng = lambda s: (s, s) if s <= 5 else (6, 21)
    a0s = {}
    for e in range(len(U)):
        a0s.setdefault(int(V[e]), set()).add(inv[int(U[e])][1][0])
    nodes = {}; U6, V6, S6, K5, K6 = [], [], [], [], []; kid6 = {}; keys6 = []
    for e in range(len(U)):
        u, v = int(U[e]), int(V[e]); vd, va = inv[v]; ua = inv[u][1]
        dst = nodes.setdefault((v, ua[0]), len(nodes))
        for a0 in a0s.get(u, ()):
            k6 = rkey(vd, tuple(rng(s) for s in (a0,) + ua + (va[-1],)))
            if k6 not in kid6:
                kid6[k6] = len(keys6); keys6.append(k6)
            U6.append(nodes.setdefault((u, a0), len(nodes))); V6.append(dst)
            S6.append(int(W[e])); K5.append(int(KI[e])); K6.append(kid6[k6])
    os.makedirs(SCR, exist_ok=True)
    G = dict(n6=len(nodes), U=np.array(U6, np.int32), V=np.array(V6, np.int32), S=np.array(S6, np.int8),
             K5=np.array(K5, np.int32), K6=np.array(K6, np.int32))
    np.savez(npz, **G)
    pickle.dump((keys5, keys6), open(kp, 'wb'))
    G.update(keys5=keys5, keys6=keys6)
    return G


# ----------------------------------------------------------------- oracles
def subwindows(k):
    """All contiguous sub-windows with >= 2 centres (canonical keys), excluding k itself."""
    ds, al = k; c = len(al); out = []
    for a in range(c):
        for b in range(a + 2, c + 1):
            if b - a == c:
                continue
            out.append(rkey(tuple(ds[a:b + 1]), tuple(al[a:b])))
    return out


class Plain:
    """Radius-4 plain status of every window key: UNSAT / SAT / TIMEOUT, merged from every source."""
    def __init__(self):
        self.st = {}; self.src = {}
        import glob
        for p in sorted(glob.glob(os.path.join(MS, '10-window-aggregate', 'data', 'oracle_cache*.jsonl'))):
            for l in open(p):
                try:
                    e = json.loads(l)
                except ValueError:
                    continue
                if e['radius'] == 4:
                    self.put(rkey(tuple(e['dirs']), tuple(map(tuple, e['alpha']))), e['status'], 'cache')
        for p, tag in ((os.path.join(HERE, '..', 's0_share_loop', 'share_oracle.jsonl'), 'share'),
                       (os.path.join(HERE, '..', 's0_k6_ceiling', 'oracle5_extra.jsonl'), 'share'),
                       (os.path.join(HERE, '..', 's0_k6_ceiling', 'oracle6.jsonl'), 'k6ceil'),
                       (OSHARE, 'here'), (OPLAIN, 'here')):
            if not os.path.exists(p):
                continue
            for l in open(p):
                r = json.loads(l)
                k = rkey(tuple(r['dirs']), tuple(tuple(a) for a in r['alpha']))
                if r['kind'] == 'plain':
                    self.put(k, r['result'], tag)
                elif r['result'] == 'SAT':
                    self.put(k, 'SAT', tag)

    def put(self, k, st, tag):
        old = self.st.get(k)
        if old == 'UNSAT' and st == 'SAT' or old == 'SAT' and st == 'UNSAT':
            raise AssertionError(f'conflict on {k}')
        if old in (None, 'TIMEOUT'):
            self.st[k] = st; self.src[k] = tag

    def blocked(self, k):
        """UNSAT itself or through a sub-window (monotone: a model restricts to every sub-window)."""
        if self.st.get(k) == 'UNSAT':
            return True
        return any(self.st.get(s) == 'UNSAT' for s in subwindows(k))

    def test(self, k, tl):
        wait_res()
        enc = ws.from_key(k)
        st, sel, cuts, sec = ws.solve(enc, tl)
        r = dict(dirs=list(k[0]), alpha=[list(a) for a in k[1]], kind='plain', k=len(k[1]), result=st,
                 witness=ws.share_exact(enc, sel, 12) if sel else None, cuts=cuts, seconds=round(sec, 2),
                 nv=enc.nv, ncl=len(enc.clauses))
        with open(OPLAIN, 'a') as f:
            f.write(json.dumps(r) + '\n')
        self.put(k, st, 'here')
        return r


def masks(G, P):
    b5 = np.array([P.blocked(k) for k in G['keys5']], bool)
    b6 = np.array([P.st.get(k) == 'UNSAT' for k in G['keys6']], bool)
    return b5, b6


def live(G, keep):
    m = prune(G['n6'], G['U'][keep], G['V'][keep])
    return np.nonzero(keep)[0][m]


# ------------------------------------------------------------------ variant A
def round_A(G, P, tl, dry=False):
    t = time.time()
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    w = G['S'][idx].astype(np.int64)
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    ce = [idx[e] for e in cyc]
    states = len(np.unique(np.concatenate([G['U'][idx], G['V'][idx]])))
    rec = dict(round=None, time=time.strftime('%H:%M:%S'), mean=str(lam), mu=round(float(lam), 5),
               m_le=round(bound_m(float(lam)), 3), len=len(cyc), syms=[int(G['S'][e]) for e in ce],
               live_states=int(states), live_edges=int(len(idx)), eval_s=round(time.time() - t, 1))
    if dry:
        return rec, []
    todo = []
    for e in ce:
        k5 = G['keys5'][G['K5'][e]]; k6 = G['keys6'][G['K6'][e]]
        todo.append((k5, k6))
    stats = dict(t5=0, t6=0, u5=0, u6=0)
    for k5, k6 in todo:
        if k5 not in P.st:
            r = P.test(k5, tl / 2); stats['t5'] += 1
            if r['result'] == 'UNSAT':
                stats['u5'] += 1; continue
        if P.st.get(k5) == 'UNSAT':
            continue
        if k6 not in P.st:
            r = P.test(k6, tl); stats['t6'] += 1
            if r['result'] == 'UNSAT':
                stats['u6'] += 1
    rec.update(stats); rec['test_s'] = round(time.time() - t - rec['eval_s'], 1)
    return rec, todo


def run_A(hours, tl):
    G = build(); P = Plain()
    print(f'k6 graph: {G["n6"]} nodes, {len(G["U"])} edges, {len(G["keys5"])} 5-keys, {len(G["keys6"])} 6-keys; '
          f'plain statuses {len(P.st)}', flush=True)
    path = os.path.join(HERE, 'rounds_A.jsonl')
    rnd0 = sum(1 for _ in open(path)) if os.path.exists(path) else 0
    t_end = time.time() + hours * 3600
    for rnd in range(rnd0, rnd0 + 100000):
        rec, _ = round_A(G, P, tl); rec['round'] = rnd
        print(json.dumps(rec), flush=True)
        with open(path, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if rec['t5'] + rec['t6'] == 0:
            print('converged: every window of the minimum cycle is SAT or timed out', flush=True); break
        if time.time() > t_end:
            print('time budget reached', flush=True); break


# ------------------------------------------------------------------ variant B
def share_oracle():
    import refine_share as rs
    rs.ORACLE = OSHARE
    O = rs.ShareOracle()                       # share_oracle.jsonl + E1 seeds
    for p in (os.path.join(HERE, '..', 's0_k6_ceiling', 'oracle5_extra.jsonl'), OSHARE):
        if os.path.exists(p):
            for l in open(p):
                O.apply(json.loads(l))
    return rs, O


def round_B(G, P, rs, O, tl, dry=False):
    t = time.time()
    b5, b6 = masks(G, P)
    keep = ~b5[G['K5']] & ~b6[G['K6']]
    idx = live(G, keep)
    lb = np.array([O.st[k]['lb'] if k in O.st else 0 for k in G['keys5']], np.int64)
    w = UNIT * G['S'][idx].astype(np.int64) + lb[G['K5'][idx]]
    _, cyc = howard(G['n6'], G['U'][idx], G['V'][idx], w)
    lam = Fr(int(w[cyc].sum()), len(cyc))
    ce = [idx[e] for e in cyc]
    rec = dict(round=None, time=time.strftime('%H:%M:%S'), lam=str(lam), mu=round(float(lam) / UNIT, 5),
               m_le=round(bound_m(float(lam) / UNIT), 3), len=len(cyc), syms=[int(G['S'][e]) for e in ce],
               T5=[int(lb[G['K5'][e]]) for e in ce], live_edges=int(len(idx)),
               keys_with_lb=int((lb > 0).sum()), eval_s=round(time.time() - t, 1))
    if dry:
        return rec
    st = dict(p5=0, p6=0, thr=0, u6=0, u5=0, thr_unsat=0)
    seen = set()
    for e in ce:
        k5 = G['keys5'][G['K5'][e]]; k6 = G['keys6'][G['K6'][e]]
        if (k5, k6) in seen:
            continue
        seen.add((k5, k6))
        if k6 not in P.st:                     # cheap first: plain 6-window
            r = P.test(k6, tl / 2); st['p6'] += 1
            if r['result'] == 'UNSAT':
                st['u6'] += 1; continue
        if P.st.get(k6) == 'UNSAT':
            continue
        s = O.get(k5)
        if not s['tested'] and k5 not in P.st:
            r = rs.run_test(k5, 'plain', None, tl / 2); O.apply(r); P.put(k5, r['result'], 'here'); st['p5'] += 1
            if r['result'] == 'UNSAT':
                st['u5'] += 1; continue
        elif P.st.get(k5) == 'UNSAT':
            continue
        T = O.next_T(k5)
        if T is None:
            continue
        r = rs.run_test(k5, 'thr', T, tl); O.apply(r); st['thr'] += 1
        st['thr_unsat'] += r['result'] == 'UNSAT'
    rec.update(st); rec['test_s'] = round(time.time() - t - rec['eval_s'], 1)
    return rec


def run_B(hours, tl):
    G = build(); P = Plain(); rs, O = share_oracle()
    rs.MEASURE_EVERY = 0
    print(f'k6 graph: {G["n6"]} nodes, {len(G["U"])} edges; share oracle {len(O.st)} keys', flush=True)
    path = os.path.join(HERE, 'rounds_B.jsonl')
    rnd0 = sum(1 for _ in open(path)) if os.path.exists(path) else 0
    t_end = time.time() + hours * 3600
    for rnd in range(rnd0, rnd0 + 100000):
        rec = round_B(G, P, rs, O, tl); rec['round'] = rnd
        print(json.dumps(rec), flush=True)
        with open(path, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if rec['p5'] + rec['p6'] + rec['thr'] == 0:
            print('converged: nothing left to test on the rigorous minimum cycle', flush=True); break
        if time.time() > t_end:
            print('time budget reached', flush=True); break


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'A':
        run_A(float(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 30)
    elif mode == 'B':
        run_B(float(sys.argv[2]), float(sys.argv[3]) if len(sys.argv) > 3 else 60)
    elif mode == 'build':
        G = build(); print(G['n6'], len(G['U']), len(G['keys5']), len(G['keys6']))
    elif mode == 'evalA':
        G = build(); P = Plain(); print(json.dumps(round_A(G, P, 0, dry=True)[0]))
    elif mode == 'evalB':
        G = build(); P = Plain(); rs, O = share_oracle(); print(json.dumps(round_B(G, P, rs, O, 0, dry=True)))
