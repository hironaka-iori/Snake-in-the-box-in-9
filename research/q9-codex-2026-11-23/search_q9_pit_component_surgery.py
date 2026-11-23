"""Allow every Q9 vertex when reconnecting trimmed components of a fixed snakepit."""

import argparse
import json
import random
from itertools import product
from pathlib import Path
from collections import Counter
from search_q9_anchored_sets import search
from search_q9_wynn_plateau import NB, verify


def components(s):
    left = set(s)
    parts = []
    while left:
        c = [left.pop()]
        for v in c:
            for w in NB[v]:
                if w in left:
                    c.append(w)
                    left.remove(w)
        group = set(c)
        ends = [v for v in c if len(group.intersection(NB[v])) <= 1]
        assert len(ends) == (1 if len(c) == 1 else 2)
        p = [min(ends)]
        remain = group - {p[0]}
        while remain:
            (v,) = remain.intersection(NB[p[-1]])
            p.append(v)
            remain.remove(v)
        assert verify(p)
        parts.append(p)
    return sorted(parts, key=lambda p: (-len(p), p))


def solve_job(job):
    k, seed, fixed, trims, extra, edges, budget = job
    status, w = search(set(fixed), set(seed), edges, budget, at_least=True)
    if w:
        assert verify(w) and len(w) >= edges + 1 and set(fixed) <= set(w)
    return dict(
        k=k,
        total=edges,
        fixed=fixed,
        trims=trims,
        extra=extra,
        status=status,
        witness=w,
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("pits", type=Path)
    ap.add_argument("--per", type=int, default=80)
    ap.add_argument("--budget", type=int, default=5000)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--max-trim", type=int, default=6)
    ap.add_argument("--interior", type=int, default=5)
    ap.add_argument("--control", action="store_true")
    ap.add_argument("--seed", type=int, default=124)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    jobs = []
    for line in args.pits.read_text().splitlines():
        r = json.loads(line)
        k = r["k"]
        if r["n"] != 9 or k not in ((1,) if args.control else (2, 3, 4, 5, 6, 7, 8)):
            continue
        pts = r["vertices"]
        comp = components(pts)
        assert len(comp) == k and len(pts) == r["L"] + k
        known = set()
        for j in range(args.per):
            trim = [
                (
                    rng.randrange(1 + (j % (args.max_trim + 1))),
                    rng.randrange(1 + (j % (args.max_trim + 1))),
                )
                for c in comp
            ]
            # Keep at least one vertex of every input component.
            for i, c in enumerate(comp):
                a, b = trim[i]
                a = min(a, (len(c) - 1) // 2)
                b = min(b, len(c) - 1 - a)
                trim[i] = (a, b)
            keep = [p[a : len(p) - b] for p, (a, b) in zip(comp, trim)]
            extra = []
            if j % 3 == 2:
                for i, p in enumerate(keep):
                    if len(p) > 15 and rng.randrange(3) != 0:
                        a = rng.randrange(3, len(p) - 9)
                        b = a + rng.randrange(1, min(args.interior, len(p) - a - 3) + 1)
                        extra.append([i, a, b])
                        keep[i] = p[:a] + p[b:]
            fixed = tuple(sorted(v for p in keep for v in p))
            if fixed in known:
                continue
            known.add(fixed)
            jobs.append(
                (k, pts, fixed, trim, extra, 191 if args.control else 192, args.budget)
            )
    rng.shuffle(jobs)
    from concurrent.futures import ProcessPoolExecutor

    with ProcessPoolExecutor(args.workers) as ex:
        for ans in ex.map(solve_job, jobs, chunksize=1):
            print(json.dumps(ans, separators=(",", ":")), flush=True)
            if ans["witness"] and not args.control:
                break


if __name__ == "__main__":
    main()
