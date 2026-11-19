#!/usr/bin/env python3
"""Censored exponential hit-rate estimate: rate(L) = #runs reaching >= L / sum over runs of min(t_hit, t_end)."""
import re, sys, glob
def runs(files):
    out = []
    for f in files:
        hits = []; tend = None
        for l in open(f):
            m = re.search(r'edges=(\d+) t=([\d.]+)', l)
            if l.startswith('BEST') and m: hits.append((int(m[1]), float(m[2])))
            if l.startswith('END'): tend = float(re.search(r'time=([\d.]+)', l)[1])
        if tend is not None: out.append((hits, tend))
    return out
def rate(rs, L):
    k = 0; T = 0.0
    for hits, tend in rs:
        th = min([t for e, t in hits if e >= L], default=None)
        if th is not None: k += 1; T += th
        else: T += tend
    return k, T
if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    rs = runs([f for g in sys.argv[3:] for f in glob.glob(g)])
    print(f"runs={len(rs)} total_time={sum(t for _, t in rs):.0f}s")
    for L in range(hi, lo-1, -1):
        k, T = rate(rs, L)
        print(f"L={L} hits={k} exposure={T:.0f}s rate={k/T*3600:.3g}/h mean_time={T/k if k else float('inf'):.4g}s")
