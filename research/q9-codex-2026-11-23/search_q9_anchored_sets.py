"""Find a Q9 snake containing every vertex shared by two aligned parent snakes."""
import argparse
import csv
from itertools import combinations
import json
import random
from pathlib import Path

from pysat.solvers import Minicard
from search_q9_wynn_plateau import NB, canonical, verify


def search(fixed, seed, edges, budget, known=None, allowed=None, reject_fragment=None, exactly_one_pairs=(), at_least=False, rooted_layer_lengths=None):
    # A vertex with three fixed neighbors, or one touching a saturated fixed
    # vertex, cannot be added. All other cube vertices remain available.
    degrees = [sum(w in fixed for w in neighbors) for neighbors in NB]
    if any(degrees[v] > 2 for v in fixed):
        return "UNSAT", None
    saturated = {v for v in fixed if degrees[v] == 2}
    free = {v for v in range(512) if v not in fixed and degrees[v] <= 2
            and saturated.isdisjoint(NB[v])}
    if allowed is not None:
        free.intersection_update(allowed)
    needed = edges + 1 - len(fixed)
    assert not (at_least and known)
    if needed > len(free) or (needed < 0 and not at_least):
        return "UNSAT", None
    with Minicard() as solver:
        def exactly(lits, k):
            if not 0 <= k <= len(lits):
                solver.add_clause([])
                return
            solver.add_atmost(lits, k)
            solver.add_atmost([-x for x in lits], len(lits)-k)

        if at_least:
            if needed>0:solver.add_atmost([-v-1 for v in free],len(free)-needed)
        else:exactly([v+1 for v in free], needed)
        for a, b in exactly_one_pairs:
            assert a not in fixed and b not in fixed and a != b
            lits = [v+1 for v in (a,b) if v in free]
            exactly(lits, 1)
        if rooted_layer_lengths is not None:
            assert {0,256}<=fixed and sum(rooted_layer_lengths)+1==edges
            for v in range(1,256):
                pair={v,v+256}
                if pair<=fixed:return "UNSAT",None
                if pair&fixed:
                    for x in pair&free:solver.add_clause([-x-1])
                elif pair<=free:solver.add_clause([-v-1,-v-257])
            for layer,length in enumerate(rooted_layer_lengths):
                for side in (0,1):
                    cells={v+layer*256 for v in range(256) if v.bit_count()%2==side}
                    exactly([v+1 for v in cells&free],(length+2-side)//2-len(cells&fixed))
        endpoints = []
        for v in fixed | free:
            if v in saturated:
                continue
            e = 513 + v
            endpoints.append(e)
            guard = [] if v in fixed else [-(v+1)]
            if guard:
                solver.add_clause([-e, v+1])
            lits = [w+1 for w in NB[v] if w in free] + [e]
            k = 2 - degrees[v]
            if k > len(lits):
                solver.add_clause(guard)
                continue
            for sub in combinations(lits, k+1):
                solver.add_clause(guard + [-x for x in sub])
            for sub in combinations(lits, len(lits)-k+1):
                solver.add_clause(guard + list(sub))
        exactly(endpoints, 2)
        for parity in (0, 1):
            # The two color classes differ by at most one.
            f = sum(v.bit_count()%2 == parity for v in fixed)
            lits = [v+1 for v in free if v.bit_count()%2 == parity]
            lo, hi = (edges+1)//2-f, (edges+2)//2-f
            if (not at_least and hi < 0) or lo > len(lits):
                return "UNSAT", None
            if not at_least and hi < len(lits):
                solver.add_atmost(lits, hi)
            if lo > 0:
                solver.add_atmost([-x for x in lits], len(lits)-lo)
        solver.set_phases([v+1 if v in seed else -v-1 for v in free])
        root = min(fixed)
        while True:
            remaining = budget - solver.accum_stats()["conflicts"]
            if remaining <= 0:
                return "UNKNOWN", None
            solver.conf_budget(remaining)
            status = solver.solve_limited()
            if status is not True:
                return ("UNSAT" if status is False else "UNKNOWN"), None
            model = set(solver.get_model())
            selected = fixed | {v for v in free if v+1 in model}
            unseen = set(selected)
            parts = []
            while unseen:
                comp = [unseen.pop()]
                for v in comp:
                    for w in NB[v]:
                        if w in unseen:
                            unseen.remove(w)
                            comp.append(w)
                parts.append(set(comp))
            if len(parts) == 1:
                ends = [v for v in selected if len(selected.intersection(NB[v])) == 1]
                assert len(ends) == 2
                path = [ends[0]]
                rest = set(selected)-{ends[0]}
                while rest:
                    v, = rest.intersection(NB[path[-1]])
                    path.append(v)
                    rest.remove(v)
                assert len(path)>=edges+1 and (at_least or len(path)==edges+1) and verify(path)
                if reject_fragment is not None:
                    fragment = reject_fragment(path)
                    if fragment:
                        # Any induced path containing this full connected subpath must
                        # traverse it contiguously, in one orientation or the other.
                        solver.add_clause([-v-1 for v in set(fragment)-fixed])
                        continue
                if known and canonical(path) in known:
                    solver.add_clause([-v-1 for v in selected-fixed])
                    continue
                return "FOUND", path
            for comp in parts:
                if root in comp:
                    continue
                border = {w+1 for v in comp for w in NB[v] if w in free-comp}
                if fixed.isdisjoint(comp):
                    border.add(-(min(comp)+1))
                solver.add_clause(list(border))


def align(path, index):
    axes = {}
    steps = [v ^ w for v, w in zip(path, path[1:])]
    for axis in steps[index:] + steps[:index]:
        axes.setdefault(axis, len(axes))
    for a in range(9):
        axes.setdefault(1 << a, len(axes))
    return frozenset(sum(1 << k for a, k in axes.items() if (v^path[index]) & a) for v in path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("bank", type=Path)
    ap.add_argument("--count", type=int, default=1000)
    ap.add_argument("--budget", type=int, default=10000)
    ap.add_argument("--min-fixed", type=int, default=110)
    ap.add_argument("--max-fixed", type=int, default=180)
    ap.add_argument("--edges", type=int, default=192)
    ap.add_argument("--seed", type=int, default=8443)
    ap.add_argument("--exclude190", type=Path, help="exclude isomorphic copies of these 190-edge snakes")
    args = ap.parse_args()
    known=set()
    if args.exclude190:
        if args.edges != 190:
            ap.error("--exclude190 requires --edges 190")
        with args.exclude190.open() as f:
            for row in csv.DictReader(f):
                path=list(map(int,row["vertices"].split()))
                assert len(path)==191 and verify(path)
                known.add(canonical(path))
    originals = [r["vertex_sequence"] for r in json.loads(args.bank.read_text())]
    assert all(verify(p) for p in originals)
    rng = random.Random(args.seed)
    pools = [[align(p[::direction], i) for p in originals for direction in (1,-1)]
             for i in (0, 23, 50, 95, 150)]
    seen = set()
    for _ in range(200000):
        a, b = rng.sample(rng.choice(pools), 2)
        fixed = a & b
        if not args.min_fixed <= len(fixed) <= args.max_fixed or fixed in seen:
            continue
        seen.add(fixed)
        status, path = search(fixed, a, args.edges, args.budget, known)
        print(json.dumps(dict(fixed=sorted(fixed),status=status,path=path)), flush=True)
        if path or len(seen) >= args.count:
            return


if __name__ == "__main__":
    main()
