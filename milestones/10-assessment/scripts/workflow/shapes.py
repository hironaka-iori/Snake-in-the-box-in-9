"""Enumerate induced path segments with m transitions in Q9 up to coordinate permutation and reversal.
Normalised by first-occurrence labelling; reversal canonicalised by min(seq, relabel(reversed))."""
import sys

def induced_ok(ts):
    # vertices p_0..p_m ; check all pairs with j>=i+2 have distance >= 2
    m = len(ts)
    p = [0]
    for t in ts:
        p.append(p[-1] ^ (1 << t))
    for i in range(m + 1):
        for j in range(i + 2, m + 1):
            if bin(p[i] ^ p[j]).count('1') <= 1:
                return False
    return True

def relabel(ts):
    mp = {}
    out = []
    for t in ts:
        if t not in mp:
            mp[t] = len(mp)
        out.append(mp[t])
    return tuple(out)

def shapes(m):
    res = []
    def rec(ts, nlab):
        if len(ts) == m:
            if induced_ok(ts):
                res.append(tuple(ts))
            return
        for t in range(min(nlab + 1, 9)):
            if ts and t == ts[-1]:
                continue
            ts.append(t)
            # prune: check prefix induced
            if induced_ok(ts):
                rec(ts, max(nlab, t + 1))
            ts.pop()
    rec([], 0)
    canon = set()
    for s in res:
        canon.add(min(s, relabel(tuple(reversed(s)))))
    return sorted(canon)

if __name__ == '__main__':
    for m in range(2, int(sys.argv[1]) + 1):
        print(m, 'transitions ->', m - 1, 'centres:', len(shapes(m)), 'shapes')
