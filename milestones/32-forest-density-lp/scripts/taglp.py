"""Direction-tagged local LP (Sherali-Adams style marginal consistency) for induced linear
forests in Q_n, with k-subcube patterns.

A tagged pattern on a k-subcube Q records, for every v in F cap Q, the set D(v) of OUTSIDE
directions (the n-k directions not spanned by Q) in which v has an F-neighbour.  The global degree
is l(v) = deg_Q(v) + |D(v)| <= 2.  Local validity: F cap Q is an induced linear forest of Q_k,
deg_Q(v) + |D(v)| <= 2, and D(u), D(v) are disjoint for adjacent u, v (no 4-cycle u, v, v+e, u+e).
Types are taken up to B_k x S_{n-k} (cube symmetry times permutations of the outside directions).

Consistency.  For a j-face R of Q (j < k) the R-view is the tagged pattern of R with its n-j
outside directions, D_R(v) = D_Q(v) + {directions of Q not in R in which v has an F-neighbour
inside Q}, ROOTED at the set T of the k-j directions of Q not spanned by R.  In a real forest every
j-face R lies in exactly C(n-j, k-j) k-subcubes, one for each (k-j)-subset T of its outside
directions.  If sigma is the type of R and O ranges over the orbits of Aut(sigma) on (k-j)-subsets,
the number of pairs (R subset Q) whose rooted type is (sigma, O) equals |O| * #{R of type sigma}.
So for every sigma, count(sigma, O) / |O| is the same for all orbits O; rooted types that no valid
k-pattern produces force count(sigma, .) = 0.  These are linear equations in x.
"""
import itertools, sys
from fractions import Fraction
from math import comb
import numpy as np
import highspy
from patterns import patterns, group, local_degrees, apply
from forestlp import face_maps


def mask_perm_table(m):
    """for each permutation pi of range(m): table mapping a mask to its image."""
    out = []
    for pi in itertools.permutations(range(m)):
        tab = []
        for x in range(1 << m):
            y = 0
            for i in range(m):
                if x >> i & 1:
                    y |= 1 << pi[i]
            tab.append(y)
        out.append((pi, tab))
    return out


_GROUPS = {}


def cube_group(j):
    if j not in _GROUPS:
        _GROUPS[j] = group(j)
    return _GROUPS[j]


_PERMS = {}


def split_perms(a, b):
    """mask tables for S_a x S_b acting on a+b directions (first a = non-root, last b = root)."""
    key = (a, b)
    if key not in _PERMS:
        tabs = []
        m = a + b
        for p1 in itertools.permutations(range(a)):
            for p2 in itertools.permutations(range(a, m)):
                pi = p1 + p2
                tab = []
                for x in range(1 << m):
                    y = 0
                    for i in range(m):
                        if x >> i & 1:
                            y |= 1 << pi[i]
                    tab.append(y)
                tabs.append(tab)
        _PERMS[key] = tabs
    return _PERMS[key]


def canon_tagged(t, j, a, b):
    """canonical form of a tagged pattern t on Q_j (entries 0 or 1+mask over a+b directions)
    under B_j x S_a x S_b."""
    best = None
    G = cube_group(j)
    for tab in split_perms(a, b):
        u = tuple(0 if x == 0 else 1 + tab[x - 1] for x in t)
        for g in G:
            w = apply(g, u)
            if best is None or w < best:
                best = w
    return best


def tagged_reps(k, m):
    """all valid tagged patterns on Q_k with m outside directions, up to B_k x S_m."""
    P = patterns(k)
    V = 1 << k
    mtabs = [tab for _, tab in mask_perm_table(m)]
    reps = []
    for cm in P.forest_reps:
        A = [v for v in range(V) if cm >> v & 1]
        stab = [g for g in P.G if sum(1 << g[v] for v in A) == cm]
        deg = local_degrees(k, A)
        opts = {v: [D for D in range(1 << m) if bin(D).count('1') <= 2 - deg[v]] for v in A}
        seen = set()
        cur = {}

        def rec(i):
            if i == len(A):
                t = [0] * V
                for v in A:
                    t[v] = 1 + cur[v]
                t = tuple(t)
                best = None
                for tab in mtabs:
                    u = tuple(0 if x == 0 else 1 + tab[x - 1] for x in t)
                    for g in stab:
                        w = apply(g, u)
                        if best is None or w < best:
                            best = w
                if best not in seen:
                    seen.add(best)
                    reps.append(best)
                return
            v = A[i]
            for D in opts[v]:
                ok = True
                for b in range(k):
                    w = v ^ (1 << b)
                    if w in cur and cur[w] & D:
                        ok = False
                        break
                if ok:
                    cur[v] = D
                    rec(i + 1)
                    del cur[v]
        rec(0)
    return reps


def build(n, k, levels=None, verbose=False):
    m = n - k
    reps = tagged_reps(k, m)
    if verbose:
        print('  %d tagged k-patterns' % len(reps), flush=True)
    V = 1 << k
    levels = range(k) if levels is None else levels
    cache = {}
    cols = []
    sigma_info = {}    # unrooted canonical sigma -> {rooted canonical: |O|}

    def rooted_orbits(j, sig):
        key = (j, sig)
        if key in sigma_info:
            return sigma_info[key]
        nd = n - j
        r = k - j
        info = {}
        for T in itertools.combinations(range(nd), r):
            rest = [d for d in range(nd) if d not in T]
            order = rest + list(T)          # new index of old direction order[i] is i
            newidx = [0] * nd
            for i, d in enumerate(order):
                newidx[d] = i
            tab = []
            for x in range(1 << nd):
                y = 0
                for d in range(nd):
                    if x >> d & 1:
                        y |= 1 << newidx[d]
                tab.append(y)
            u = tuple(0 if x == 0 else 1 + tab[x - 1] for x in sig)
            rc = canon_tagged(u, j, nd - r, r)
            info[rc] = info.get(rc, 0) + 1
        sigma_info[key] = info
        return info

    unrooted_of = {}
    for t in reps:
        A = [v for v in range(V) if t[v]]
        ldQ = local_degrees(k, A)
        cnt = {}
        for j in levels:
            for verts in face_maps(k, j):
                # directions of Q not in R, in a fixed order
                spanned = 0
                for u in verts:
                    spanned |= u ^ verts[0]
                others = [b for b in range(k) if not spanned >> b & 1]
                tR = []
                for u in verts:
                    if not t[u]:
                        tR.append(0)
                        continue
                    D = t[u] - 1               # bits 0..m-1: outside directions of Q
                    for i, b in enumerate(others):
                        if t[u ^ (1 << b)]:
                            D |= 1 << (m + i)  # bits m..: the root directions
                    tR.append(1 + D)
                tR = tuple(tR)
                key = (j, tR)
                if key not in cache:
                    rc = canon_tagged(tR, j, m, k - j)
                    cache[key] = rc
                rc = cache[key]
                cnt[(j, rc)] = cnt.get((j, rc), 0) + 1
        cols.append(cnt)
        for (j, rc) in cnt:
            if (j, rc) not in unrooted_of:
                unrooted_of[(j, rc)] = (j, canon_tagged(rc, j, 0, n - j))
    # rows
    rows = []
    sigmas = sorted(set(unrooted_of.values()))
    for (j, sig) in sigmas:
        info = rooted_orbits(j, sig)
        orbs = sorted(info)
        base = orbs[0]
        for o in orbs[1:]:
            rows.append(((j, o), info[o], (j, base), info[base]))
    # assemble coefficients: row r: cnt(o)/|O| - cnt(base)/|Obase|
    rowcoef = []
    for t_i, cnt in enumerate(cols):
        d = {}
        for r, (o, so, b, sb) in enumerate(rows):
            v = Fraction(cnt.get(o, 0), so) - Fraction(cnt.get(b, 0), sb)
            if v:
                d[r] = v
        rowcoef.append(d)
    obj, end = [], []
    for t in reps:
        A = [v for v in range(V) if t[v]]
        ld = local_degrees(k, A)
        obj.append(Fraction(len(A), V))
        end.append(Fraction(sum(2 - ld[v] - bin(t[v] - 1).count('1') for v in A), V))
    return dict(n=n, k=k, reps=reps, rows={r: i for i, r in enumerate(rows)}, cols=rowcoef, obj=obj, end=end)


if __name__ == '__main__':
    from forestlp import solve, certify
    n, k = int(sys.argv[1]), int(sys.argv[2])
    M = build(n, k, verbose=True)
    print('n=%d k=%d tagged: %d patterns, %d rows' % (n, k, len(M['reps']), len(M['rows'])), flush=True)
    for c in range(0, 2 ** (n - 2) + 1):
        val, rd, x = solve(M, 2 * c / 2 ** n)
        print('c=%2d  LP |F| <= %.4f' % (c, val * 2 ** n), flush=True)
