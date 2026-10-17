import json, sys, collections, random
from itertools import combinations
PAIRS = list(combinations(range(9), 2))
def alphas(vs):
    S = set(vs); out = []
    for x in vs:
        a = 0
        for i, j in PAIRS:
            if (x ^ (1 << i)) not in S and (x ^ (1 << j)) not in S and (x ^ (1 << i) ^ (1 << j)) not in S:
                a += 1
        out.append(a)
    return out
def empties(vs):
    S = set(vs); e = 0
    for x in range(512):
        for i, j in PAIRS:
            if x >> i & 1 or x >> j & 1: continue
            if not ({x, x | 1 << i, x | 1 << j, x | 1 << i | 1 << j} & S): e += 1
    return e
if __name__ == '__main__':
    bank = json.load(open(sys.argv[1]))
    L = lambda x: json.loads(x) if isinstance(x, str) else x
    allw = collections.Counter(); amin = collections.Counter(); hist = collections.Counter()
    for e in bank:
        v = L(e['vertex_sequence']); a = alphas(v)
        hist.update(a); amin[min(a)] += 1
        for i in range(1, len(a) - 3):
            allw[tuple(a[i:i+3])] += 1
    print('alpha histogram (bank, all vertices):', sorted(hist.items()))
    v = L(bank[0]['vertex_sequence']); a = alphas(v)
    T = sum(a); E = empties(v); n = len(v)
    print('bank[0]: v=%d T=%d emptySquares=%d  check E+2T+70v (E counted x4) =' % (n, T, E), 4 * E + 2 * T + 70 * n)
    low = sorted((w for w in allw if sum(w) <= 12), key=sum)
    print('internal 3-windows with sum<=12 in bank:', [(w, allw[w]) for w in low][:40])
    print('min 3-window sum in bank:', min(sum(w) for w in allw), ' min 2-window sum:', min(a1 + a2 for (a1, a2, _) in allw))
