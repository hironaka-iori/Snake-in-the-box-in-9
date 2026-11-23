"""Replace two neighboring Q6 visits simultaneously, retaining all other blocks."""

import argparse
import json
from pathlib import Path
from search_q9_anchored_sets import search as native_search
from search_q9_wynn_plateau import NB
from pysat.formula import CNF
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical195
from itertools import combinations


def search(fixed, seed, target, budget, allowed=None, at_least=True):
    forced = {v: sum(w in fixed for w in NB[v]) for v in range(512)}
    sat2 = {v for v in fixed if forced[v] == 2}
    free = sorted(
        v
        for v in allowed - fixed
        if forced[v] <= 2 and all(w not in sat2 for w in NB[v])
    )
    F = set(free)
    form = CNF()
    top = 1024
    if any(forced[v] > 2 for v in fixed):
        return "UNSAT", None

    def card(lits, lim, kind):
        nonlocal top
        if lim < 0 or lim > len(lits):
            if kind == "atleast" and lim <= 0:
                return
            form.append([])
            return
        clause = getattr(CardEnc, kind)(
            lits, bound=lim, top_id=top, encoding=EncType.totalizer
        )
        form.extend(clause.clauses)
        top = max(top, clause.nv)

    card([v + 1 for v in free], max(0, target + 1 - len(fixed)), "atleast")
    for c in (0, 1):
        fs = [v + 1 for v in free if v.bit_count() % 2 == c]
        need = (target + 1) // 2 - sum(v.bit_count() % 2 == c for v in fixed)
        card(fs, max(0, need), "atleast")
    ends = []
    for v in fixed | F:
        if v in sat2:
            continue
        guard = [] if v in fixed else [-v - 1]
        e = 513 + v
        ends.append(e)
        if guard:
            form.append([-e, v + 1])
        adj = [w + 1 for w in NB[v] if w in F] + [e]
        need = 2 - forced[v]
        for z in combinations(adj, need + 1):
            form.append(guard + [-a for a in z])
        if len(adj) < need:
            form.append(guard)
            continue
        for z in combinations(adj, len(adj) - need + 1):
            form.append(guard + list(z))
    card(ends, 2, "equals")
    root = min(fixed)
    with Cadical195(bootstrap_with=form) as sol:
        sol.set_phases([v + 1 if v in seed else -v - 1 for v in free])
        while True:
            left = budget - sol.accum_stats()["conflicts"]
            if left < 1:
                return "UNKNOWN", None
            sol.conf_budget(left)
            r = sol.solve_limited()
            if r is not True:
                return ("UNSAT" if r is False else "UNKNOWN"), None
            model = set(sol.get_model())
            S = fixed | {v for v in F if v + 1 in model}
            groups = []
            rest = set(S)
            while rest:
                q = [rest.pop()]
                for v in q:
                    for w in NB[v]:
                        if w in rest:
                            rest.remove(w)
                            q.append(w)
                groups.append(set(q))
            if len(groups) == 1:
                ends = [v for v in S if len(set(NB[v]) & S) == 1]
                assert len(ends) == 2
                q = ends[:1]
                S.remove(q[0])
                while S:
                    (v,) = S.intersection(NB[q[-1]])
                    q.append(v)
                    S.remove(v)
                assert len(q) >= target + 1 and verify(q)
                return "FOUND", q
            for g in groups:
                if root in g:
                    continue
                border = {w + 1 for v in g for w in NB[v] if w in F - g}
                if fixed.isdisjoint(g):
                    border.add(-min(g) - 1)
                sol.add_clause(list(border))


from search_q9_wynn_plateau import verify


def load(line):
    fields = line.split()
    n = int(fields[0])
    assert len(fields) == 1 + 2 * n
    sites = []
    for j in range(n):
        cell = int(fields[1 + 2 * j])
        mask = int(fields[2 + 2 * j], 16)
        sites.append((cell, {64 * cell + x for x in range(64) if mask >> x & 1}))
    return sites


def run(src, target, budget, width=2, selected=None):
    for row, line in enumerate(src.read_text().splitlines()):
        seq = load(line)
        seed = set.union(*(s for _, s in seq))
        assert len(seed) == 192
        for i in range(len(seq) - width + 1):
            if selected is not None and (row, i) not in selected:
                continue
            window = range(i, i + width)
            cells = {seq[j][0] for j in window}
            fixed = set.union(*(s for j, (_, s) in enumerate(seq) if j not in window))
            allowed = fixed | {v for v in range(512) if v >> 6 in cells}
            bounded, w = search(
                fixed, seed, target, budget, allowed=allowed, at_least=True
            )
            if w:
                assert verify(w) and len(w) >= target + 1
            yield {
                "row": row,
                "visits": list(window),
                "target": target,
                "fixed": len(fixed),
                "status": bounded,
                "witness": w,
            }
            if w and target >= 192:
                return


if __name__ == "__main__":
    import sys

    sel = None
    if len(sys.argv) > 5:
        sel = {
            (d["row"], d["visits"][0])
            for l in Path(sys.argv[5]).read_text().splitlines()
            if (d := json.loads(l))["status"] == "UNKNOWN"
        }
    for d in run(
        Path(sys.argv[1]),
        int(sys.argv[2]),
        int(sys.argv[3]),
        int(sys.argv[4]) if len(sys.argv) > 4 else 2,
        sel,
    ):
        print(json.dumps(d, separators=(",", ":")), flush=True)
        if int(sys.argv[2]) == 191 and d["witness"]:
            break
