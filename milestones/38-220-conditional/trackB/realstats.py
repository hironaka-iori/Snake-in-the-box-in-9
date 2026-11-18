"""Per-vertex alpha / corner share (M=12) statistics of the 131 bank snakes, and the floor each
quantity imposes on any local method (a real snake satisfies every local constraint).
Floor: largest v with mean weight >= needed(v); needed(v) for alpha units = 9214/v - 35
(combined alpha + share12/24 uses 18428/(2v) - 35 = the same)."""
import json, itertools, sys
bank = json.load(open(sys.argv[1] if len(sys.argv) > 1 else '../../../work/bank9.json'))
def stats(seq):
    S = set(seq); n = len(seq); A = []; SH = []
    for i, x in enumerate(seq):
        used = set()
        if i > 0: used.add((x ^ seq[i-1]).bit_length() - 1)
        if i < n-1: used.add((x ^ seq[i+1]).bit_length() - 1)
        a = sum(1 for p, q in itertools.combinations(range(9), 2) if p not in used and q not in used
                and (x ^ 1 << p ^ 1 << q) not in S and (x ^ 1 << p) not in S and (x ^ 1 << q) not in S)
        sh = 0
        for k in range(9):
            q = x ^ 1 << k
            if q in S: continue
            e0 = sum(1 for a2, b in itertools.combinations(range(9), 2)
                     if not ({q, q ^ 1 << a2, q ^ 1 << b, q ^ 1 << a2 ^ 1 << b} & S))
            d = sum(1 for t in range(9) if q ^ 1 << t in S)
            sh += 12 * e0 // d
        A.append(a); SH.append(sh)
    return A, SH
def floor_v(mu):          # largest v with 9214/v - 35 <= mu
    return int(9214 / (35 + mu))
rows = []
for sn in bank:
    A, SH = stats(sn['vertex_sequence'])
    rows.append((A[1:-1], SH[1:-1]))
allA = [a for A, _ in rows for a in A]; allS = [s for _, S in rows for s in S]
n = len(allA)
print('vertices', n, 'mean alpha', sum(allA)/n, 'mean share12', sum(allS)/n)
for c in (6, 7, 8, 9, 10, 12, 21):
    mu = sum(min(a, c) for a in allA) / n
    print(f'cap {c}: mean {mu:.3f}  floor v={floor_v(mu)} m~{floor_v(mu)-1}')
mu = sum(a + s/24 for a, s in zip(allA, allS)) / n
print('combined alpha+share/24 mean', round(mu, 3), 'floor m~', floor_v(mu)-1)
for c in (6, 7, 8):
    mu = sum(min(a, c) + s/24 for a, s in zip(allA, allS)) / n
    print(f'combined capped {c}', round(mu, 3), 'floor m~', floor_v(mu)-1)
# min over 7-windows of combined
w7 = min(sum(24*A[i+j] + S[i+j] for j in range(7)) for A, S in rows for i in range(len(A)-6))
w7s = min(sum(S[i+j] for j in range(7)) for A, S in rows for i in range(len(A)-6))
print('min real 7-window 24a+share', w7, 'min real 7-window share', w7s, 'needed for 220 ~', round(7*24*(9214/222-35)))
from collections import Counter
print('alpha histogram', sorted(Counter(allA).items()))
