"""Integer potential of smallest range for the weights q*w - p.

A potential is any pi with pi[v] <= pi[u] + (q w - p) on every edge u -> v.  Its range can be
forced below Rmax by a virtual source s with edges s -> v of weight Rmax and v -> s of weight 0
(so 0 <= pi[v] - pi[s] <= Rmax); a feasible system has no negative cycle and Bellman-Ford then
converges.  Binary search over Rmax gives the smallest range.  Bellman-Ford is capped (an
infeasible bound never converges); a returned potential is re-checked on every edge.
"""
import numpy as np


def bf_bounded(n, U, V, W, p, q, rmax, max_iter=4000):
    """rmax: a number (uniform upper bound) or an array of per-node upper bounds."""
    order = np.argsort(V, kind='stable')
    U, V, W = U[order], V[order], W[order]
    w = q * W - p
    starts = np.searchsorted(V, np.arange(n + 1))
    has = starts[1:] > starts[:-1]
    seg = starts[:-1][has]
    # pi[s] = 0 throughout: the bound edges become 0 <= pi[v] <= rmax
    pi = np.array(np.broadcast_to(rmax, (n,)), dtype=np.int64)
    for it in range(max_iter):
        cand = pi[U] + w
        best = np.minimum.reduceat(cand, seg)
        new = pi.copy()
        new[has] = np.minimum(pi[has], best)
        if (new < 0).any():
            return None                      # pi[v] < pi[s]: a negative cycle through s
        if (new == pi).all():
            return pi
        pi = new
    return None


def check(U, V, W, p, q, pi):
    return bool((q * W - p + pi[U] - pi[V] >= 0).all())


def min_range_potential(n, U, V, W, p, q, hi, max_iter=4000):
    """Smallest rmax in [0, hi] with a feasible potential; returns (rmax, pi) or (None, None)."""
    lo, best = 0, None
    while lo <= hi:
        mid = (lo + hi) // 2
        pi = bf_bounded(n, U, V, W, p, q, mid, max_iter)
        if pi is not None and check(U, V, W, p, q, pi):
            best = (mid, pi); hi = mid - 1
        else:
            lo = mid + 1
    return best if best else (None, None)


def init_sums(A):
    """Sum of the k-1 symbols of every state (the counts carried in the state), times A.den when the
    edges carry share weights (den * symbol + LB: the first state's counts get no share credit)."""
    digs = np.array([[(t // A.ns ** j) % A.ns + 1 for j in range(A.k - 1)] for t in range(A.m1)]).sum(1)
    return (getattr(A, 'den', 1) * np.tile(digs, len(A.shapes))).astype(np.int64)


def min_start_potential(A, U, V, W, p, q, hi, max_iter=4000):
    """Smallest D with a potential 0 <= pi(v) <= D + q * init(v): the sequence bound then reads
    q * sum(counts) >= p * (m - L) + q - D (first internal count >= 1, the next k-1 in the state).
    Weighted edges: q * (den * init + sum w') >= p * steps - D; see share_lb.bound_edges."""
    init = init_sums(A)
    lo, best = -q * int(init.max()), None
    while lo <= hi:
        mid = (lo + hi) // 2
        ub = mid + q * init
        if (ub < 0).all():
            lo = mid + 1; continue
        pi = bf_bounded(A.n, U, V, W, p, q, np.maximum(ub, -1), max_iter)
        if pi is not None and check(U, V, W, p, q, pi) and (pi <= ub).all() and (pi >= 0).all():
            best = (mid, pi); hi = mid - 1
        else:
            lo = mid + 1
    return best if best else (None, None)
