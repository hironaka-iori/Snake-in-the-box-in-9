import json, itertools
from exact_bound import bound, sym, excl12
base = {(2,2,2)}
cands = sorted(excl12 - base, key=lambda p: (sum(p), p))
for goal in (244, 243, 242):
    best = None
    for k in range(1, len(cands)+1):
        for S in itertools.combinations(cands, k):
            if bound(sym(base | set(S))) <= goal:
                best = S; break
        if best: break
    print(goal, 'needs', len(best), 'new window exclusions, e.g.', best)
