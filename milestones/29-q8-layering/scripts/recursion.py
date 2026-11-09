"""Recursive layering upper bounds g_{n+1}(c) <= R_{n+1}(c) from upper bounds on g_n.

A forest F in Q_{n+1} with c' <= c paths and f vertices has f - c' edges, so some direction j
carries k <= floor((f - c')/(n+1)) of them.  Cutting along j gives c' + k pieces, c1 in one half
and c2 in the other, with |c1 - c2| <= c' (each path's pieces alternate).  Hence
    f <= max { g_n(c1) + g_n(c2) : c1 + c2 = c' + k, |c1 - c2| <= c', k <= floor((f-c')/(n+1)) },
and R_{n+1}(c) is the largest f passing this test for some c' <= c (capped by Huang, 2^n).
"""
import json
from layer import load, table_funcs


def R_next(n, g, cmax):
    half = 1 << n           # Huang bound in Q_{n+1}
    out = {}
    for c in range(1, cmax + 1):
        best = 0
        for f in range(1, half + 1):
            ok = False
            for cp in range(1, c + 1):
                if f < cp:
                    continue
                K = (f - cp) // (n + 1)
                for k in range(K + 1):
                    P = cp + k
                    for c1 in range(P + 1):
                        c2 = P - c1
                        if abs(c1 - c2) <= cp and g(c1) + g(c2) >= f:
                            ok = True; break
                    if ok: break
                if ok: break
            if ok:
                best = f
        out[c] = best
    return out


if __name__ == '__main__':
    tab = load('../data/g6.jsonl')
    g6, _, _ = table_funcs(tab, 32)
    R7 = R_next(6, g6, 40)
    R8 = R_next(7, lambda p: 0 if p <= 0 else R7.get(p, 64), 40)
    print('R7(c) (from exact g6):', R7)
    print('R8(c) (from R7):', R8)
    json.dump({'R7': R7, 'R8': R8}, open('../data/recursion.json', 'w'))
