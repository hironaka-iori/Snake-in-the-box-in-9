"""Search for an arbitrary induced second arm in Q8 with one crossing in Q9.

An optional radius bounds the number of omitted vertices of a known second arm.
Each disconnected SAT model yields a necessary connectivity clause.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from pysat.solvers import Minicard
from search_q9_wynn_plateau import WYNN, verify


def vertices(steps):
    path = [0]
    for axis in steps:
        path.append(path[-1] ^ (1 << int(axis)))
    return path


def solve(lower, target, hint, radius, budget):
    if lower[0] != 0 or not verify(lower) or max(lower) >= 256:
        raise ValueError("invalid lower arm")
    # x(v) = v+1. y(v) = v+257 designates the second endpoint.
    allowed = set(range(256)) - set(lower[1:])
    neighbors = {v: [v ^ (1 << i) for i in range(8) if v ^ (1 << i) in allowed]
                 for v in allowed}
    end_parity = target % 2
    ends = {v for v in allowed if v and v.bit_count() % 2 == end_parity}
    with Minicard() as sat:
        def exact(lits, n):
            if n < 0 or n > len(lits):
                sat.add_clause([])
                return
            sat.add_atmost(lits, n)
            sat.add_atmost([-x for x in lits], len(lits) - n)

        sat.add_clause([1])
        exact([v+257 for v in ends], 1)
        for parity in (0, 1):
            size = target//2+1 if parity==0 else (target+1)//2
            exact([v+1 for v in allowed if v.bit_count()%2==parity], size)
        for v, nbr in neighbors.items():
            adj = [u+1 for u in nbr]
            if not v:
                exact(adj, 1)
                continue
            if v in ends:
                sat.add_clause([-(v+257), v+1])
                adj.append(v+257)
            # If v is selected, exactly two incident slots must be filled.
            for triple in combinations(adj, 3):
                sat.add_clause([-(v+1), *(-a for a in triple)])
            sat.add_clause([-(v+1), *adj])
            for a in adj:
                sat.add_clause([-(v+1), *(b for b in adj if a != b)])
        for i,j in combinations(range(8),2):
            for v in allowed:
                if v & ((1<<i)|(1<<j)): continue
                face = (v,v^(1<<i),v^(1<<j),v^(1<<i)^(1<<j))
                if all(u in allowed for u in face):
                    sat.add_clause([-(u+1) for u in face])
        if hint is not None:
            assert hint[0] == 0 and set(hint) <= allowed and verify(hint)
            if radius is not None:
                sat.add_atmost([-(v+1) for v in hint], radius)
                # The target fixes the difference between additions and removals.
                sat.add_atmost([v+1 for v in sorted(allowed-set(hint))],
                               radius + target + 1 - len(hint))
            sat.set_phases([v+1 for v in hint])
        cuts = 0
        while True:
            left = budget - sat.accum_stats()["conflicts"]
            if left <= 0: return "UNKNOWN", cuts, None
            sat.conf_budget(left)
            result = sat.solve_limited()
            if result is not True:
                return ("UNSAT" if result is False else "UNKNOWN"), cuts, None
            model = set(sat.get_model())
            selected = {v for v in allowed if v+1 in model}
            path = [0]
            used = {0}
            while choices := [u for u in neighbors[path[-1]] if u in selected-used]:
                assert len(choices)==1
                path.append(choices[0])
                used.add(choices[0])
            if used == selected:
                full = list(reversed(lower)) + [v+256 for v in path]
                assert len(path)==target+1 and verify(full)
                return "FOUND", cuts, full
            # Any selected vertex in a disconnected component needs an exit
            # to reach the root in every connected solution.
            unseen = selected-used
            while unseen:
                comp = {next(iter(unseen))}
                stack = list(comp)
                while stack:
                    fresh = set(neighbors[stack.pop()]) & unseen - comp
                    comp.update(fresh)
                    stack.extend(fresh)
                unseen -= comp
                border = {u+1 for v in comp for u in neighbors[v] if u not in comp}
                sat.add_clause([-(min(comp)+1), *sorted(border)])
                cuts += 1


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("bank",type=Path)
    ap.add_argument("--radius",type=int)
    ap.add_argument("--budget",type=int,default=20000)
    ap.add_argument("--controls",action="store_true")
    ap.add_argument("--source",choices=["wynn","bank"],default="wynn")
    args=ap.parse_args()
    paths = [vertices(WYNN)] if args.source=="wynn" else [
        row["vertex_sequence"] for row in json.loads(args.bank.read_text())]
    stats=Counter()
    seedpairs=set()
    for p in paths:
        assert verify(p)
        steps=[(a^b).bit_length()-1 for a,b in zip(p,p[1:])]
        for d in range(9):
            if steps.count(d)!=1:continue
            mid=steps.index(d)
            for a,b in [(steps[:mid][::-1],steps[mid+1:]),(steps[mid+1:],steps[:mid][::-1])]:
                labels={}
                norm=lambda seq: tuple(labels.setdefault(i,len(labels)) for i in seq)
                pair=(norm(a),norm(b))
                if pair in seedpairs:continue
                seedpairs.add(pair)
                lower,hint=map(vertices,pair)
                target=192-len(lower)
                if args.controls:
                    ok,_,full=solve(lower,len(hint)-1,hint,0,args.budget)
                    assert ok=="FOUND" and len(full)==len(p)
                status,cuts,full=solve(lower,target,hint,args.radius,args.budget)
                stats[status]+=1
                if full is not None:
                    print(json.dumps({"edges":len(full)-1,"vertices":full}),flush=True)
                    return
    print(json.dumps({"source":args.source,"radius":args.radius,"conflict_budget":args.budget,
                      "controls":args.controls,"outcomes":dict(stats)}),flush=True)


if __name__ == "__main__":
    main()
