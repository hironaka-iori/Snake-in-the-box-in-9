"""Lift a square-fiber projection while allowing independent flips of base corners."""
import argparse
import json
import random
from collections import defaultdict
from itertools import combinations
from pathlib import Path

from pysat.solvers import Minicard
from search_q9_square_fiber_lift import check, projections


def solve(base, hint, mutable, target, cap, all_neighbors=False):
    n = len(base)
    next_id = 0

    def variables(count):
        nonlocal next_id
        first = next_id + 1
        next_id += count
        return list(range(first, next_id + 1))

    occ = [variables(4) for _ in base]
    ports = [variables(4) for _ in range(n + 1)]
    parity = [[], []]
    at_base = defaultdict(list)
    choices = {}
    with Minicard() as sat:
        for port in ports:
            sat.add_clause(port)
            sat.add_atmost(port, 1)
        sat.add_clause([ports[0][0]])
        for i, (v, row) in enumerate(zip(base, occ)):
            start, end = ports[i:i+2]
            sat.add_atmost(row, 3)
            for u in range(4):
                parity[((v ^ base[0]).bit_count() + u.bit_count()) % 2].append(row[u])
                sat.add_clause([-start[u], row[u]])
                sat.add_clause([-end[u], row[u]])
                for w in range(4):
                    if u ^ w == 3:
                        sat.add_clause([-start[u], -end[w], row[u ^ 1], row[u ^ 2]])
                    else:
                        for c in set(range(4)) - {u, w}:
                            sat.add_clause([-start[u], -end[w], -row[c]])
            if i:
                for c in range(4):
                    sat.add_clause([-occ[i-1][c], -row[c], ports[i][c]])
            if i not in mutable:
                at_base[v].append((i, row))
                continue
            anchors = [base[j] for j in (i-1, i+1) if 0 <= j < n]
            if all_neighbors:
                locations = [anchors[0] ^ (1 << bit) for bit in range(7)]
                locations = [loc for loc in locations if all((loc ^ z).bit_count() == 1 for z in anchors)]
            else:
                locations = [v, base[i-1] ^ base[i+1] ^ v]
            assert v in locations and len(locations) == len(set(locations))
            if len(locations) == 2:
                flip, = variables(1)
                alternative, = set(locations) - {v}
                menu = [(v, -flip), (alternative, flip)]
            else:
                menu = list(zip(locations, variables(len(locations))))
                flags = [flag for _, flag in menu]
                sat.add_clause(flags)
                sat.add_atmost(flags, 1)
            choices[i] = menu
            for loc, active in menu:
                selected = variables(4)
                for s, used in zip(selected, row):
                    sat.add_clause([-used, -active, s])
                    sat.add_clause([-s, active])
                    sat.add_clause([-s, used])
                at_base[loc].append((i, selected))
        for loc, visits in at_base.items():
            for (_, a), (_, b) in combinations(visits, 2):
                for c in range(4):
                    for d in (c, c ^ 1, c ^ 2):
                        sat.add_clause([-a[c], -b[d]])
            for k in range(7):
                other = loc ^ (1 << k)
                if other <= loc:
                    continue
                for i, a in visits:
                    for j, b in at_base.get(other, []):
                        if abs(i-j) > 1:
                            for c in range(4):
                                sat.add_clause([-a[c], -b[c]])
        for group, minimum in zip(parity, ((target+2)//2, (target+1)//2)):
            sat.add_atmost([-x for x in group], len(group) - minimum)
        phase = [flag if loc == base[i] else -flag for i, menu in choices.items() for loc, flag in menu]
        for i, fiber in enumerate(hint):
            phase.extend([ports[i][fiber[0]], ports[i+1][fiber[-1]]])
            phase.extend(occ[i][c] if c in fiber else -occ[i][c] for c in range(4))
        sat.set_phases(phase)
        sat.conf_budget(cap)
        status = sat.solve_limited()
        if status is not True:
            return ("UNSAT" if status is False else "UNKNOWN"), None
        model = set(sat.get_model())
        out = []
        for i, v in enumerate(base):
            if i in choices:
                v, = [loc for loc, flag in choices[i] if flag in model]
            a = next(c for c in range(4) if ports[i][c] in model)
            b = next(c for c in range(4) if ports[i+1][c] in model)
            fiber = [a]
            if a ^ b == 3:
                fiber.append(next(c for c in (a ^ 1, a ^ 2) if occ[i][c] in model))
            if a != b:
                fiber.append(b)
            out.extend(v + 128*c for c in fiber)
        assert len(out) >= target + 1 and check(out)
        return "FOUND", out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bank",type=Path)
    ap.add_argument("limit",type=int)
    ap.add_argument("cap",type=int)
    ap.add_argument("--target",default=192,type=int)
    ap.add_argument("--width",default=18,type=int)
    args = ap.parse_args()
    rng = random.Random(935029)
    unique = {}
    for line in args.bank.read_text().splitlines():
        vertices = list(map(int, line.split()))
        assert len(vertices) == 192 and check(vertices)
        steps = [(a ^ b).bit_length()-1 for a,b in zip(vertices,vertices[1:])]
        for p,h in projections(steps):
            unique.setdefault(bytes(p), h)
    bases = sorted(unique)
    rng.shuffle(bases)
    for p in bases[:args.limit]:
        start = rng.randrange(1, len(p)-args.width)
        ids = [i for i in range(start,start+args.width,2) if p[i-1] != p[i+1]]
        status, path = solve(p, unique[p], ids, args.target, args.cap)
        print(json.dumps([status,p.hex(),ids,path],separators=(",",":")),flush=True)
        if path:
            break


if __name__ == "__main__":
    main()
