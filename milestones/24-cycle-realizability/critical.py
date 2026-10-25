"""Long REALIZABLE walks in the critical subgraph of the k6 full product.

Let lam be the minimum cycle mean and pi an integer Bellman-Ford potential for Q s - P.
G0 = transitions of reduced cost 0 (Q s - P + pi(u) - pi(v) = 0).  Every walk in G0 of T
transitions has count sum exactly lam T + (pi(start) - pi(end))/Q, so it is as bad as the
critical cycle.  Shape-realizability cuts (forbidding shape sequences that no induced path
follows) can only raise the bound if every long G0 walk is unrealizable.

This script searches for a concrete induced path of Q9 whose automaton walk can be lifted
to G0 (the counts are free: we track the set of G0 states compatible with the directions
so far), and as long as possible.  A path of N edges gives a realizable G0 walk of N - 7
transitions.  Randomised DFS with restarts; the witness is re-checked independently
(induced path; every step an allowed G0 transition of the product).

  nice -n 10 python critical.py keys235|allknown [seconds] [seed]
"""
import sys, os, json, time, random
import numpy as np
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import cutloop as CL
from shapes import canon

NC = CL.NC


def main():
    which = sys.argv[1]
    budget = float(sys.argv[2]) if len(sys.argv) > 2 else 600
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    shp, u, v, s, nkeys = CL.base_graph(which)
    n = len(shp) * NC
    m = CL.prune(n, u, v); u, v, s = u[m], v[m], s[m]
    bf = CL.BF(n, u, v, s)
    lam, cyc, pi, it = CL.mcm(bf, Fr(4))
    P, Q = lam.numerator, lam.denominator
    rc = Q * s - P + pi[u] - pi[v]
    assert rc.min() >= 0
    z = rc == 0
    u0, v0, s0 = u[z], v[z], s[z]
    print(f'{which}: lam {lam}, potential range {pi.max() - pi.min()}, G0 has {z.sum()} of {len(u)} transitions', flush=True)
    sid = {c: i for i, c in enumerate(shp)}
    # G0 edges grouped by (source shape, target shape): arrays of (count idx src, count idx dst)
    grp = {}
    a_, b_ = u0 // NC, v0 // NC
    for a, b in set(zip(a_.tolist(), b_.tolist())):
        mm = (a_ == a) & (b_ == b)
        grp[(a, b)] = (u0[mm] % NC, v0[mm] % NC, s0[mm])
    succ = {}
    for (a, b) in grp:
        succ.setdefault(a, set()).add(b)
    rnd = random.Random(seed)
    best = (0, None)
    t0 = time.time()
    # start states: every G0 shape, with every count vector having a G0 out-edge
    starts = sorted(succ)

    def run(start_shape, node_cap):
        w = list(shp[start_shape])
        vs = [0]
        for d in w:
            vs.append(vs[-1] ^ (1 << d))
        inpath = set(vs)
        R = np.zeros(NC, bool)
        for b in succ[start_shape]:
            R[grp[(start_shape, b)][0]] = True
        nodes = [0]
        bestl = [0, list(w)]

        def go(seq, a, R):
            nodes[0] += 1
            if len(seq) > bestl[0] + 7:
                bestl[0] = len(seq) - 7; bestl[1] = list(seq)
            if nodes[0] > node_cap:
                return
            labels = list(range(9)); rnd.shuffle(labels)
            last = vs[-1]
            for d in labels:
                if d in seq[-6:]:
                    if canon(seq[-6:] + [d]) not in sid:
                        continue
                b = sid.get(canon(seq[-6:] + [d]))
                if b is None or (a, b) not in grp:
                    continue
                # label d must give exactly the shape transition a -> b
                nv = last ^ (1 << d)
                if nv in inpath or any((nv ^ (1 << k)) in inpath and (nv ^ (1 << k)) != last for k in range(9)):
                    continue
                cu, cv, _ = grp[(a, b)]
                sel = R[cu]
                if not sel.any():
                    continue
                R2 = np.zeros(NC, bool); R2[cv[sel]] = True
                seq.append(d); vs.append(nv); inpath.add(nv)
                go(seq, b, R2)
                seq.pop(); vs.pop(); inpath.discard(nv)
                if nodes[0] > node_cap:
                    return
        go(list(w), start_shape, R)
        return bestl[0], bestl[1]

    sys.setrecursionlimit(10000)
    tries = 0
    while time.time() - t0 < budget:
        st = rnd.choice(starts)
        L, seq = run(st, rnd.choice([2000, 20000, 200000]))
        tries += 1
        if L > best[0]:
            best = (L, seq)
            print(f'{time.time() - t0:.0f}s try {tries}: G0 walk of {L} transitions, path {L + 7} edges', flush=True)
    L, seq = best
    # independent re-check: induced path, and a G0 lift exists (forward set propagation)
    vs = [0]
    for d in seq:
        vs.append(vs[-1] ^ (1 << d))
    assert len(set(vs)) == len(vs)
    assert all(bin(vs[i] ^ vs[j]).count('1') >= 2 for j in range(len(vs)) for i in range(j - 1))
    # reconstruct an explicit count lift (backward pass over the reachable sets)
    shapes_seq = [sid[canon(seq[t:t + 7])] for t in range(len(seq) - 6)]
    sets = []
    a0 = shapes_seq[0]
    R = np.zeros(NC, bool)
    R[grp[(a0, shapes_seq[1])][0]] = True
    sets.append(R)
    for t in range(len(shapes_seq) - 1):
        cu, cv, _ = grp[(shapes_seq[t], shapes_seq[t + 1])]
        R2 = np.zeros(NC, bool); R2[cv[sets[-1][cu]]] = True
        assert R2.any()
        sets.append(R2)
    c = int(np.flatnonzero(sets[-1])[0])
    lift = [c]; counts = []
    for t in range(len(shapes_seq) - 2, -1, -1):
        cu, cv, ss = grp[(shapes_seq[t], shapes_seq[t + 1])]
        k = np.flatnonzero((cv == c) & sets[t][cu])[0]
        counts.append(int(ss[k])); c = int(cu[k]); lift.append(c)
    counts.reverse()
    T = len(counts)
    tot = sum(counts)
    res = dict(which=which, lam=str(lam), G0_transitions=int(z.sum()), path_edges=len(seq),
               G0_walk_transitions=T, count_sum=tot, mean=tot / T, directions=seq,
               new_counts=counts, seconds=round(time.time() - t0), seed=seed)
    print(json.dumps({k: v_ for k, v_ in res.items() if k not in ('directions', 'new_counts')}), flush=True)
    out = os.path.join(HERE, 'data', f'critical_walk_{which}.json')
    old = json.load(open(out)) if os.path.exists(out) else None
    if old is None or old['path_edges'] < res['path_edges']:
        json.dump(res, open(out, 'w'))


if __name__ == '__main__':
    main()
