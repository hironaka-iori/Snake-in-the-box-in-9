#!/usr/bin/env python3
"""Exact window repair of Q_n snakes with CP-SAT (single worker).

Take a snake v0..vL from the pool, free a window of w consecutive vertices
(interior window: keep v0..vi and vj..vL, free v_{i+1}..v_{j-1}; or an end
window: keep v0..vi, free the tail), and solve exactly for the longest
replacement such that the result is again an induced path.  Model: binary x_u
on candidate vertices (not kept, no kept neighbour other than the anchors);
each chosen vertex has exactly 2 chosen-or-anchor neighbours (an end window
allows exactly one chosen vertex of degree 1); each anchor has exactly one
chosen neighbour.  Such solutions are a path plus induced cycles; cycles are
removed by lazy cuts (sum over cycle <= |cycle|-1) and re-solving.
Any snake longer than the input is validated with check.check before it is
written as a BEST line.

usage: window_repair.py N pool_glob... -o out.txt [-t seconds] [-s seed]
       [-wmin 30] [-wmax 60] [-tl 60] [-min 190]
"""
import sys, glob, random, time
from ortools.sat.python import cp_model
from check import check

def load_pool(paths, n, minedges):
    pool = {}
    for p in paths:
        for line in open(p):
            if not (line.startswith("BEST") or line[:1].isdigit()):
                continue
            if ":" in line:
                line = line.split(":", 1)[1]
            seq = [int(t) for t in line.split()]
            if len(seq) - 1 >= minedges and check(n, seq) is None:
                pool[tuple(seq)] = 1
    return [list(s) for s in pool]

def nbrs(u, n):
    return [u ^ (1 << b) for b in range(n)]

def repair(seq, i, j, n, tl, end):
    """end=False: keep seq[:i+1], seq[j:]; free between.  end=True: keep seq[:i+1]."""
    keep = seq[:i + 1] + ([] if end else seq[j:])
    anchors = [seq[i]] + ([] if end else [seq[j]])
    K = set(keep)
    A = set(anchors)
    cand = []
    for u in range(1 << n):
        if u in K:
            continue
        if any(w in K and w not in A for w in nbrs(u, n)):
            continue
        cand.append(u)
    C = set(cand)
    m = cp_model.CpModel()
    x = {u: m.NewBoolVar(f"x{u}") for u in cand}
    if end:
        e = {u: m.NewBoolVar(f"e{u}") for u in cand}   # e_u: u is the free end
        m.Add(sum(e.values()) <= 1)
        for u in cand:
            m.AddImplication(e[u], x[u])
    for u in cand:
        deg = sum(x[w] for w in nbrs(u, n) if w in C) + sum(1 for w in nbrs(u, n) if w in A)
        target = 2 - (e[u] if end else 0)
        m.Add(deg == target).OnlyEnforceIf(x[u])
    for a in anchors:
        s = sum(x[w] for w in nbrs(a, n) if w in C)
        if end:
            m.Add(s <= 1)   # tail may also be empty
        else:
            m.Add(s == 1)
    if end:
        # if anchor has no chosen neighbour then nothing chosen at all
        s = sum(x[w] for w in nbrs(anchors[0], n) if w in C)
        m.Add(sum(x.values()) <= len(cand) * s)
        m.Add(sum(e.values()) == s)
    m.Maximize(sum(x.values()))
    t0 = time.time()
    while True:
        left = tl - (time.time() - t0)
        if left <= 1:
            return None
        sv = cp_model.CpSolver()
        sv.parameters.num_workers = 1
        sv.parameters.max_time_in_seconds = left
        st = sv.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            return None
        S = {u for u in cand if sv.Value(x[u])}
        # walk the path from the first anchor
        path, prev, cur = [], seq[i], None
        nx = [w for w in nbrs(seq[i], n) if w in S]
        seen = set()
        cur = nx[0] if nx else None
        while cur is not None and cur not in seen:
            seen.add(cur); path.append(cur)
            nxt = [w for w in nbrs(cur, n) if w in S and w != prev and w not in seen]
            prev, cur = cur, (nxt[0] if nxt else None)
        rest = S - seen
        if not rest:
            new = seq[:i + 1] + path + ([] if end else seq[j:])
            return new, st == cp_model.OPTIMAL
        # rest consists of induced cycles: add a cut per component
        while rest:
            u = rest.pop(); comp = {u}; stack = [u]
            while stack:
                y = stack.pop()
                for w in nbrs(y, n):
                    if w in rest:
                        rest.discard(w); comp.add(w); stack.append(w)
            m.Add(sum(x[w] for w in comp) <= len(comp) - 1)

def main():
    a = sys.argv[1:]
    n = int(a.pop(0))
    opt = {"-o": None, "-t": "3600", "-s": "1", "-wmin": "30", "-wmax": "60", "-tl": "60", "-min": "190"}
    paths = []
    while a:
        k = a.pop(0)
        if k in opt:
            opt[k] = a.pop(0)
        else:
            paths += glob.glob(k)
    rng = random.Random(int(opt["-s"]))
    pool = load_pool(paths, n, int(opt["-min"]))
    out = open(opt["-o"], "a")
    out.write(f"# pool={len(pool)} seed={opt['-s']}\n"); out.flush()
    best = max(len(s) - 1 for s in pool)
    T = float(opt["-t"]); t0 = time.time(); tries = gains = 0; stats = {}
    while time.time() - t0 < T:
        seq = rng.choice(pool)
        if rng.random() < 0.5:
            seq = seq[::-1]
        L = len(seq)
        w = rng.randint(int(opt["-wmin"]), int(opt["-wmax"]))
        end = rng.random() < 0.25
        if end:
            i = L - 1 - w; j = L
        else:
            i = rng.randint(0, L - 2 - w); j = i + w + 1
        r = repair(seq, i, j, n, float(opt["-tl"]), end)
        tries += 1
        if r is None:
            stats["timeout"] = stats.get("timeout", 0) + 1; continue
        new, optimal = r
        d = len(new) - len(seq)
        key = f"d{d:+d}" + ("" if optimal else "nonopt")
        stats[key] = stats.get(key, 0) + 1
        if tries % 200 == 0:
            out.write(f"STAT tries={tries} t={time.time()-t0:.0f} pool={len(pool)} {sorted(stats.items())}\n")
        if check(n, new) is None and d > 0:
            gains += 1
            pool.append(new)
            out.write(f"BEST v={len(new)} edges={len(new)-1} t={time.time()-t0:.0f} : {' '.join(map(str, new))}\n")
            best = max(best, len(new) - 1)
        elif d == 0 and new != seq and len(pool) < 20000 and check(n, new) is None:
            pool.append(new)   # equal-length variant widens the pool
        out.flush()
    out.write(f"STAT final {sorted(stats.items())}\n"); out.write(f"END seed={opt['-s']} tries={tries} gains={gains} best={best} time={time.time()-t0:.0f}\n")

if __name__ == "__main__":
    main()
