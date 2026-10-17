"""Per-vertex combined charge c(x) = alpha(x) + sum over empty squares Q adjacent to x of 2/(#selected adjacent to Q).
Sum_x c(x) = T + 2 n0 = 9214 - 35 v when every empty square is adjacent to S (true for all bank snakes).
Needed average to exclude v=L+2: 9214/(L+2) - 35.  Report minimal k-window means of c along each snake."""
import json, itertools, math
from fractions import Fraction
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
PAIRS = list(itertools.combinations(range(9), 2))
res = {}
allc = []
for idx, e in enumerate(bank):
    seq = e['vertex_sequence']; S = set(seq); pos = {x: i for i, x in enumerate(seq)}
    c = [0.0] * len(seq)
    for i, x in enumerate(seq):
        c[i] += sum(all(w not in S for w in (x ^ 1 << a, x ^ 1 << b, x ^ 1 << a ^ 1 << b)) for a, b in PAIRS)
    for base in range(512):
        for a, b in PAIRS:
            if base >> a & 1 or base >> b & 1: continue
            sq = [base, base | 1 << a, base | 1 << b, base | 1 << a | 1 << b]
            if any(w in S for w in sq): continue
            adj = {w ^ 1 << k for w in sq for k in range(9)} & S
            for y in adj:
                c[pos[y]] += 2 / len(adj)
    assert abs(sum(c) - (9214 - 35 * len(seq))) < 1e-6
    allc.append(c)
print('mean charge per vertex (exact, v=192):', (9214 - 35 * 192) / 192)
print('needed mean to prove a(9)<=L:', {L: round(9214 / (L + 2) - 35, 3) for L in (191, 196, 200, 210, 220, 230, 240)})
for k in [1, 3, 5, 10, 20, 40, 80, 120, 160, 190]:
    best = min(min(sum(c[i:i + k]) / k for i in range(1, len(c) - k)) for c in allc)
    v = math.floor(9214 / (35 + best))
    print('k=%3d  min realized window mean charge %.3f -> averaging ceiling: edges >= %d' % (k, best, v - 1))
