"""Exact inner optimisation for a fixed outer (Q4-level) transition word.

A Q9 vertex is (inner x in Q5, outer p in Q4). The outer word fixes the
fiber of every segment; CP-SAT chooses each segment's induced path in Q5.
Every reported path is re-verified on all unordered pairs."""
import json, sys, collections, time
from ortools.sat.python import cp_model
NI = 5; NV = 1 << NI
ADJ = [[x ^ (1 << k) for k in range(NI)] for x in range(NV)]
def solve(word, seconds=60, workers=4, target=None, hint=None, nlight=4):
    m = len(word); fib = [0]
    for w in word: fib.append(fib[-1] ^ (1 << w))
    S = range(m + 1)
    M = cp_model.CpModel()
    sel = [[M.new_bool_var('') for x in range(NV)] for s in S]
    st = [[None] * NV for s in S]; en = [[None] * NV for s in S]
    for s in S:
        arcs = []
        for x in range(NV):
            st[s][x] = M.new_bool_var(''); en[s][x] = M.new_bool_var('')
            arcs += [(NV, x, st[s][x]), (x, NV, en[s][x]), (x, x, sel[s][x].Not())]
        arc = {}
        for x in range(NV):
            for y in ADJ[x]:
                arc[x, y] = M.new_bool_var(''); arcs.append((x, y, arc[x, y]))
        M.add_circuit(arcs)
        for x in range(NV):
            for y in ADJ[x]:
                if x < y:  # chordless inside the segment
                    M.add_bool_or([sel[s][x].Not(), sel[s][y].Not(), arc[x, y], arc[y, x]])
    for s in range(m):
        for x in range(NV):
            M.add(en[s][x] == st[s + 1][x])
    for s in S:
        for t in S:
            if t <= s: continue
            d = bin(fib[s] ^ fib[t]).count('1')
            if d == 0:
                for x in range(NV):
                    M.add_bool_or([sel[s][x].Not(), sel[t][x].Not()])
                    for y in ADJ[x]:
                        M.add_bool_or([sel[s][x].Not(), sel[t][y].Not()])
            elif d == 1:
                for x in range(NV):
                    if t == s + 1:
                        M.add_bool_or([sel[s][x].Not(), sel[t][x].Not(), en[s][x]])
                    else:
                        M.add_bool_or([sel[s][x].Not(), sel[t][x].Not()])
    M.add(st[0][0] == 1)
    total = sum(sel[s][x] for s in S for x in range(NV))
    if target: M.add(total >= target)
    else: M.maximize(total)
    if hint:
        for s in S:
            for x in range(NV): M.add_hint(sel[s][x], int(x in hint[s]))
    sol = cp_model.CpSolver(); sol.parameters.max_time_in_seconds = seconds
    sol.parameters.num_workers = workers
    t0 = time.time(); r = sol.solve(M)
    out = dict(status=sol.status_name(r), secs=round(time.time() - t0, 1))
    if r in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        out['value'] = int(sol.objective_value) if not target else None
        out['bound'] = sol.best_objective_bound if not target else None
        # reconstruct the Q9 path (inner bits low, outer bits high)
        path = []
        for s in S:
            nxt = {}
            start = [x for x in range(NV) if sol.value(st[s][x])][0]
            seg = [start]
            # follow chosen arcs: recompute via selected set and adjacency order
            chosen = {x for x in range(NV) if sol.value(sel[s][x])}
            prev = None; cur = start
            while len(seg) < len(chosen):
                nx = [y for y in ADJ[cur] if y in chosen and y != prev and y not in seg]
                prev, cur = cur, nx[0]; seg.append(cur)
            for i, x in enumerate(seg):
                if s > 0 and i == 0: continue  # crossing duplicates previous end (inner)
                path.append(x | (fib[s] << NI))
            if s > 0:
                path.insert(len(path) - len(seg) + 1, seg[0] | (fib[s] << NI))
        out['path'] = path
    return out
def verify(path, n=9):
    if len(set(path)) != len(path): return False
    for i in range(len(path)):
        for j in range(i + 1, len(path)):
            adj = bin(path[i] ^ path[j]).count('1') == 1
            if adj != (j == i + 1): return False
    return True
