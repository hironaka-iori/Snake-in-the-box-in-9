import json, collections, sys
L = lambda x: json.loads(x) if isinstance(x, str) else x
def decompose(e):
    t = L(e['transition_sequence']); v = L(e['vertex_sequence'])
    c = collections.Counter(t)
    light = sorted(range(9), key=lambda k: (c[k], k))[:4]
    heavy = [k for k in range(9) if k not in light]
    lpos = {k: i for i, k in enumerate(light)}
    word = [lpos[k] for k in t if k in lpos]
    def remap(x):
        inner = sum(((x >> k) & 1) << i for i, k in enumerate(heavy))
        outer = sum(((x >> k) & 1) << i for i, k in enumerate(light))
        return inner, outer
    rv = [remap(x) for x in v]
    x0, p0 = rv[0]
    rv = [(x ^ x0, p ^ p0) for x, p in rv]
    segs = []
    for x, p in rv:
        if not segs or segs[-1][0] != p: segs.append((p, []))
        segs[-1][1].append(x)
    return word, [set(s) for _, s in segs], len(v)
