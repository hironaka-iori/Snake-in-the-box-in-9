import json, sys, collections
bank = json.load(open(sys.argv[1]))
L = lambda x: json.loads(x) if isinstance(x, str) else x
def analyze(e, nlight=4):
    t = L(e['transition_sequence']); v = L(e['vertex_sequence'])
    c = collections.Counter(t)
    order = sorted(range(9), key=lambda k: (c[k], k))
    light = order[:nlight]; heavy = order[nlight:]
    def outer(x): return tuple((x >> k) & 1 for k in light)
    def inner(x): return tuple((x >> k) & 1 for k in heavy)
    segs = []
    for x in v:
        o = outer(x)
        if not segs or segs[-1][0] != o: segs.append([o, []])
        segs[-1][1].append(inner(x))
    fib = collections.defaultdict(set)
    for o, xs in segs: fib[o].update(xs)
    visits = collections.Counter(o for o, _ in segs)
    # projection overlap between adjacent fibers
    overl = 0
    for o in fib:
        for k in range(nlight):
            o2 = tuple(b ^ (i == k) for i, b in enumerate(o))
            if o2 in fib and o < o2:
                overl += len(fib[o] & fib[o2])
    # parity classes union overlap
    A = set().union(*(fib[o] for o in fib if sum(o) % 2 == 0))
    B = set().union(*(fib[o] for o in fib if sum(o) % 2 == 1))
    return dict(nseg=len(segs), nfib=len(fib), maxvisit=max(visits.values()),
                sizes=sorted((len(s) for s in fib.values()), reverse=True),
                seglens=[len(xs) for _, xs in segs], adj_overlap=overl,
                A=len(A), B=len(B), AB=len(A & B))
res = [analyze(e) for e in bank]
print('segments: ', collections.Counter(r['nseg'] for r in res).most_common(8))
print('fibers used (of 16): ', collections.Counter(r['nfib'] for r in res))
print('max visits of one fiber: ', collections.Counter(r['maxvisit'] for r in res))
print('example fiber sizes (vertices per Q5 fiber):', res[0]['sizes'])
print('example segment lengths:', res[0]['seglens'])
mx = collections.Counter(max(r['sizes']) for r in res); print('max fiber size dist', sorted(mx.items()))
print('adjacent-fiber projection overlaps (= crossing count expected):', collections.Counter(r['adj_overlap'] for r in res).most_common(6))
print('even-class union |A|, odd-class union |B|, |A&B| (first 8):', [(r['A'], r['B'], r['AB']) for r in res[:8]])
print('AB overlap distribution:', collections.Counter(r['AB'] for r in res).most_common(10))
# Q6 x Q3 split
res3 = [analyze(e, 3) for e in bank]
print('Q6xQ3: segments', collections.Counter(r['nseg'] for r in res3).most_common(6), 'fibers used', collections.Counter(r['nfib'] for r in res3))
print('Q6xQ3 fiber sizes example', res3[0]['sizes'], 'max', collections.Counter(max(r['sizes']) for r in res3))
