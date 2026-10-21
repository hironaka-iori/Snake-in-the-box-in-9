"""Huang slack: how far can a snake be augmented while keeping lambda_max < 3?

Huang: every U in Q9 with |U| >= 257 has lambda_1(A_s[U]) >= 3, where A_s is
the signed adjacency matrix with every square negative.  So if S is a snake
and X a set of outside vertices with lambda_1(A_s[S u X]) < 3, then
|S| + |X| <= 256.  A purely local sufficient condition is Gershgorin on
A_s[U]^2:   deg_U(x) + e_U(x) <= 8 for all x in U, where e_U(x) counts the
z in U at distance 2 from x having exactly one common neighbour in U (two
common neighbours in U cancel, since every square is negative).

For each set S we grow X greedily (random order, several restarts) under
(a) the exact spectral test and (b) the Gershgorin test, and report |S|+|X|.
"""
import json, sys, random
import numpy as np

n = 9
NV = 1 << n


def sign(x, i):
    return -1.0 if bin(x >> (i + 1)).count('1') & 1 else 1.0


def lam_max(U):
    U = list(U)
    idx = {u: k for k, u in enumerate(U)}
    M = np.zeros((len(U), len(U)))
    for u in U:
        for i in range(n):
            w = u ^ (1 << i)
            if w in idx:
                M[idx[u], idx[w]] = sign(min(u, w), i)
    return np.linalg.eigvalsh(M)[-1]


def gersh_ok_at(x, U):
    deg = sum(1 for i in range(n) if x ^ (1 << i) in U)
    e = 0
    for i in range(n):
        for j in range(i + 1, n):
            z = x ^ (1 << i) ^ (1 << j)
            if z in U:
                c = (x ^ (1 << i) in U) + (x ^ (1 << j) in U)
                if c == 1:
                    e += 1
    return deg + e <= 8


def gersh_ok(U, touched):
    return all(gersh_ok_at(x, U) for x in touched if x in U)


def ball2(y):
    out = {y}
    for i in range(n):
        out.add(y ^ (1 << i))
        for j in range(i + 1, n):
            out.add(y ^ (1 << i) ^ (1 << j))
    return out


def augment(S, mode, seed):
    rng = random.Random(seed)
    U = set(S)
    cand = [y for y in range(NV) if y not in U]
    rng.shuffle(cand)
    # prefer low outside-degree candidates
    cand.sort(key=lambda y: sum(1 for i in range(n) if y ^ (1 << i) in U))
    for y in cand:
        U.add(y)
        ok = gersh_ok(U, ball2(y)) if mode == 'g' else lam_max(U) < 3 - 1e-9
        if not ok:
            U.remove(y)
    return len(U)


def kdist(S):
    S = set(S)
    h = {}
    for y in range(NV):
        if y not in S:
            k = sum(1 for i in range(n) if y ^ (1 << i) in S)
            h[k] = h.get(k, 0) + 1
    return dict(sorted(h.items()))


if __name__ == '__main__':
    import os; root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..') + '/'
    sets = []
    bank = json.load(open(root + 'work/bank9.json'))
    for k in (0, 45, 100):
        sets.append(('bank%d' % k, bank[k]['vertex_sequence']))
    for name in ('adversary208', 'adversary224'):
        sets.append((name, json.load(open(root + 'milestones/11-local-ceiling/data/%s.json' % name))['S']))
    modes = sys.argv[1] if len(sys.argv) > 1 else 'gs'
    for name, S in sets:
        print(name, 'v=%d' % len(S), 'lam_max(S)=%.3f' % lam_max(S), 'k-dist', kdist(S), flush=True)
        for mode in modes:
            res = [augment(S, mode, s) for s in range(2 if mode == 's' else 4)]
            print('   mode', mode, '|S u X| =', res, flush=True)
