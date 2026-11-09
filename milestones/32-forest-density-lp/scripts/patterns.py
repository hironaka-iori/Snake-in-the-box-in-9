"""Labelled local patterns of induced linear forests in a k-subcube, up to the symmetry of Q_k.

A pattern on Q_k is a tuple t of length 2^k: t[v] = 0 if v is not in F, else 1 + l(v), where
l(v) in {0,1,2} is the GLOBAL degree of v in F.  Validity (for a forest in Q_n):
  * A = {v : t[v] > 0} induces a linear forest in Q_k (max degree 2, acyclic);
  * ld(v) <= l(v) <= 2, where ld is the degree inside Q_k;
  * the out-degrees o(v) = l(v) - ld(v) admit an assignment of out-direction sets
    D(v) subset of the n-k outside directions, |D(v)| = o(v), with D(u), D(v) disjoint for
    adjacent u, v in A (otherwise u, v, v+e, u+e is a 4-cycle of F).
"""
import itertools
from functools import lru_cache


def group(k):
    """All automorphisms of Q_k as tuples g with g[v] = image of v."""
    out = []
    for perm in itertools.permutations(range(k)):
        base = []
        for v in range(1 << k):
            w = 0
            for i in range(k):
                if v >> i & 1:
                    w |= 1 << perm[i]
            base.append(w)
        for s in range(1 << k):
            out.append(tuple(b ^ s for b in base))
    return out


def local_degrees(k, A):
    s = set(A)
    return {v: sum((v ^ (1 << i)) in s for i in range(k)) for v in A}


def is_linear_forest(k, A):
    s = set(A)
    deg = local_degrees(k, A)
    if any(d > 2 for d in deg.values()):
        return False
    e = sum(deg.values()) // 2
    seen, comp = set(), 0
    for v in A:
        if v in seen:
            continue
        comp += 1
        st = [v]
        seen.add(v)
        while st:
            u = st.pop()
            for i in range(k):
                w = u ^ (1 << i)
                if w in s and w not in seen:
                    seen.add(w)
                    st.append(w)
    return len(A) - e == comp


def out_feasible(k, t, nout):
    """Is there an assignment of out-direction sets as in the module docstring?"""
    A = [v for v in range(1 << k) if t[v]]
    deg = local_degrees(k, A)
    o = {v: t[v] - 1 - deg[v] for v in A}
    if any(x > nout for x in o.values()):
        return False
    if nout >= 2:
        # adjacent vertices of A have ld >= 1, so o <= 1 for them; the forest is bipartite,
        # so two directions always suffice
        return True
    # nout == 1 (or 0): adjacent out-vertices would share the unique direction
    for v in A:
        if o[v]:
            for i in range(k):
                w = v ^ (1 << i)
                if w in o and o[w]:
                    return False
    return True


def apply(g, t):
    r = [0] * len(t)
    for v, x in enumerate(t):
        r[g[v]] = x
    return tuple(r)


class Patterns:
    """All labelled patterns on Q_k up to symmetry (independent of n; n enters via validity)."""

    def __init__(self, k):
        self.k = k
        self.V = 1 << k
        self.G = group(k)
        # forests up to symmetry
        forests = {}
        for m in range(1 << self.V):
            A = [v for v in range(self.V) if m >> v & 1]
            if not is_linear_forest(k, A):
                continue
            cm = min(sum(1 << g[v] for v in A) for g in self.G)
            forests.setdefault(cm, None)
        self.forest_reps = sorted(forests)
        reps = []
        for cm in self.forest_reps:
            A = [v for v in range(self.V) if cm >> v & 1]
            stab = [g for g in self.G if sum(1 << g[v] for v in A) == cm]
            deg = local_degrees(k, A)
            seen = set()
            for labs in itertools.product(*[range(deg[v], 3) for v in A]):
                t = [0] * self.V
                for v, l in zip(A, labs):
                    t[v] = 1 + l
                t = tuple(t)
                c = min(apply(g, t) for g in stab)
                if c not in seen:
                    seen.add(c)
                    reps.append(c)
        self.reps = reps
        self.index = {t: i for i, t in enumerate(reps)}

    def canon(self, t):
        """canonical rep of t and the list of g with apply(g, t) == rep."""
        best, gs = None, []
        for g in self.G:
            u = apply(g, t)
            if best is None or u < best:
                best, gs = u, [g]
            elif u == best:
                gs.append(g)
        return best, gs


@lru_cache(None)
def patterns(k):
    return Patterns(k)


if __name__ == '__main__':
    for k in range(1, 5):
        P = patterns(k)
        print(k, 'forest orbits', len(P.forest_reps), 'labelled orbits', len(P.reps))
