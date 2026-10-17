"""Independent square census for bank snakes.
For every coordinate square of Q9 (36 pairs x 128 base points = 4608) count selected corners.
n_k = #squares with k selected corners. T = n_1 (singleton squares, each has one selected corner).
W = #internal path vertices whose two neighbours differ in distinct coordinates (always all internal).
Check: n0+n1+n2+n3+n4 = 4608, n1+2n2+3n3+4n4 = 36 v, n4 = 0, n3 = W = v-2,
identity 2E+4T+144v = 36864+4W with E = 4 n0, and E+2T+70v = 18428.
Also per-vertex alpha, and distance distribution.
"""
import json, sys, itertools, statistics
from fractions import Fraction
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
PAIRS = list(itertools.combinations(range(9), 2))

def check_snake(vs):
    S = set(vs)
    assert len(S) == len(vs)
    for a, b in zip(vs, vs[1:]):
        assert bin(a ^ b).count('1') == 1
    # induced: number of adjacent pairs == v-1
    adj = sum(1 for x in vs for k in range(9) if (x ^ (1 << k)) in S) // 2
    assert adj == len(vs) - 1, (adj, len(vs))

def census(vs):
    S = set(vs)
    n = [0] * 5
    for base in range(512):
        for i, j in PAIRS:
            if base >> i & 1 or base >> j & 1:
                continue
            c = sum(w in S for w in (base, base | 1 << i, base | 1 << j, base | 1 << i | 1 << j))
            n[c] += 1
    # alpha per vertex
    alpha = []
    for x in vs:
        a = 0
        for i, j in PAIRS:
            if all(w not in S for w in (x ^ 1 << i, x ^ 1 << j, x ^ 1 << i ^ 1 << j)):
                a += 1
        alpha.append(a)
    # W: selected centres with two selected neighbours in distinct coordinates
    W = 0
    for x in vs:
        nb = [k for k in range(9) if (x ^ 1 << k) in S]
        W += len(nb) * (len(nb) - 1) // 2  # pairs of distinct coordinates with both neighbours selected
    # ordered distance-2 pairs
    y = [0] * 10
    for x in vs:
        for z in vs:
            y[bin(x ^ z).count('1')] += 1
    return n, alpha, W, y

rows = []
idx = [int(a) for a in sys.argv[1:]] or list(range(len(bank)))
for k in idx:
    vs = bank[k]['vertex_sequence']
    check_snake(vs)
    v = len(vs)
    n, alpha, W, y = census(vs)
    T = sum(alpha)
    E = 4 * n[0]
    assert n[4] == 0
    assert T == n[1], (T, n[1])
    assert sum(n) == 4608 and n[1] + 2 * n[2] + 3 * n[3] == 36 * v
    rows.append(dict(k=k, v=v, n=n, T=T, W=W, E=E,
                     id1=2 * E + 4 * T + 144 * v - (36864 + 4 * W),
                     id2=E + 2 * T + 70 * v - 18428,
                     W_eq=W == v - 2, n3_eq_W=n[3] == W,
                     y2=y[2], y2_formula=23 * v + 10 - T,
                     amin=min(alpha), aint_min=min(alpha[1:-1]), aend=(alpha[0], alpha[-1]),
                     Tv=T / v, twoT_E_v=(2 * T + E) / v, twon0_v=2 * n[0] / v))
json.dump(rows, open('/tmp/claude-0/-home-user-Snake-in-the-box-in-9/54df6b79-3551-5be0-97ec-edf141639c5c/scratchpad/wf/census.json', 'w'))
bad = [r for r in rows if r['id1'] or r['id2'] or not r['W_eq'] or not r['n3_eq_W'] or r['y2'] != r['y2_formula']]
print('snakes checked:', len(rows), ' identity failures:', len(bad))
for r in rows[:5]:
    print({q: r[q] for q in ('k', 'v', 'n', 'T', 'W', 'E', 'id1', 'id2', 'W_eq', 'y2', 'y2_formula', 'amin', 'aend')})
Tv = [r['Tv'] for r in rows]; n0 = [r['n'][0] for r in rows]; T = [r['T'] for r in rows]
print('T: min %d max %d mean %.2f ; T/v min %.4f (k=%d) max %.4f mean %.4f' % (min(T), max(T), statistics.mean(T), min(Tv), rows[Tv.index(min(Tv))]['k'], max(Tv), statistics.mean(Tv)))
print('n0 (empty squares): min %d max %d mean %.2f' % (min(n0), max(n0), statistics.mean(n0)))
print('(2T+E)/v all equal:', set(round(r['twoT_E_v'], 6) for r in rows))
print('2n0/v: min %.3f max %.3f; 2T/v min %.3f max %.3f' % (min(r['twon0_v'] for r in rows), max(r['twon0_v'] for r in rows), 2 * min(Tv), 2 * max(Tv)))
print('min alpha histogram:', sorted(statistics.multimode([r['amin'] for r in rows])), {a: sum(r['amin'] == a for r in rows) for a in range(10)})
