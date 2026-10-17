import json, itertools, statistics, collections
bank = json.load(open('/home/user/Snake-in-the-box-in-9/work/bank9.json'))
PAIRS = list(itertools.combinations(range(9), 2))
def dist_to_S(S):
    d = {v: (0 if v in S else 99) for v in range(512)}
    frontier = list(S); r = 0
    while frontier:
        r += 1; nf = []
        for v in frontier:
            for k in range(9):
                w = v ^ 1 << k
                if d[w] > r: d[w] = r; nf.append(w)
        frontier = nf
    return d
stats = collections.Counter(); per = []
for e in bank:
    S = set(e['vertex_sequence']); v = len(S); d = dist_to_S(S)
    hist = collections.Counter(d.values())
    n0 = 0; sqdist = collections.Counter(); charge = collections.Counter()
    for base in range(512):
        for i, j in PAIRS:
            if base >> i & 1 or base >> j & 1: continue
            sq = [base, base | 1 << i, base | 1 << j, base | 1 << i | 1 << j]
            if any(w in S for w in sq): continue
            n0 += 1
            sqdist[min(d[w] for w in sq)] += 1
            # number of selected vertices adjacent to the square (distance 1 from some corner)
            adjsel = {w ^ 1 << k for w in sq for k in range(9)} & S
            charge[len(adjsel)] += 1
    per.append(dict(v=v, n0=n0, far=hist.get(2, 0) + hist.get(3, 0), N1=hist[1], sqdist=dict(sqdist), charge=dict(charge)))
print('unselected vertices adjacent to S (|N(S)\\S|): mean %.1f ; vertices at distance>=2: min %d max %d mean %.2f' % (
    statistics.mean(p['N1'] for p in per), min(p['far'] for p in per), max(p['far'] for p in per), statistics.mean(p['far'] for p in per)))
tot = collections.Counter(); ch = collections.Counter()
for p in per:
    tot.update(p['sqdist']); ch.update(p['charge'])
print('empty squares by min corner distance to S (all bank):', dict(tot))
print('empty squares by #selected vertices adjacent to the square:', sorted(ch.items()))
print('n0/v mean %.3f' % statistics.mean(p['n0'] / p['v'] for p in per))
