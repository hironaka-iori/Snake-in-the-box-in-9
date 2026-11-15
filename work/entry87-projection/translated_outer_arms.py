"""Two translated 49-vertex outer arms for a 95-vertex middle in the eight-cube."""
import json
from collections import Counter
from functools import lru_cache
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

from solve import defects, save
from two_eight_layers import decode


@lru_cache(None)
def quotient(delta):
    representatives = [min(x, x ^ delta) for x in range(256)]
    graph = {v: Counter(representatives[v ^ (1 << j)] for j in range(8))
             for v in sorted(set(representatives))}
    assert all(v not in adjacent for v, adjacent in graph.items())
    return representatives, graph


def decide(path):
    delta = path[-1]
    rep, graph = quotient(delta)
    blocked = {rep[v] for v in path[1:-1]}
    reached = {0}
    pending = [0]
    while pending:
        v = pending.pop()
        new = {w for w, mult in graph[v].items() if mult == 1} - blocked - reached
        reached.update(new)
        pending.extend(new)
    sides = [[v for v in sorted(reached) if v.bit_count() % 2 == parity] for parity in (0, 1)]
    counts = list(map(len, sides))
    if counts[0] < 25 or counts[1] < 24:
        return dict(reason="parity capacity", counts=counts)
    degree = {v: sum(mult for w, mult in graph[v].items() if w in reached) for v in reached}
    edges = sum(degree[v] for v in sides[0])
    for side, target in zip(sides, (25, 24)):
        edges -= sum(sorted((degree[v] for v in side if v), reverse=True)[:len(side)-target])
    if edges > 48:
        return dict(reason="edge count", counts=counts, minimum=edges)
    # A rooted path requires at most two neighbours everywhere, including
    # across both arms in the lift. First test this necessary relaxation.
    from itertools import combinations
    ids = IDPool()
    chosen = {v: ids.id(v) for v in sorted(reached)}
    with Solver(name="cadical195") as sat:
        sat.add_clause([chosen[0]])
        for side, target in zip(sides, (25, 24)):
            sat.append_formula(CardEnc.equals([chosen[v] for v in side], bound=target,
                                               vpool=ids, encoding=EncType.totalizer).clauses)
        for v in sorted(reached):
            singles = []
            for w, mult in graph[v].items():
                if w not in reached:
                    continue
                if mult > 1:
                    sat.add_clause([-chosen[v], -chosen[w]])
                else:
                    singles.append(chosen[w])
            for group in combinations(singles, 2 if v == 0 else 3):
                sat.add_clause([-chosen[v], *[-w for w in group]])
        disconnected = 0
        while sat.solve():
            positive = set(sat.get_model())
            selected = {v for v in reached if chosen[v] in positive}
            arm = [0]
            used = {0}
            while True:
                next_sites = {arm[-1] ^ (1 << j) for j in range(8)
                              if rep[arm[-1] ^ (1 << j)] in selected - used}
                if not next_sites:
                    break
                assert len(next_sites) == 1
                arm.append(next_sites.pop())
                used.add(rep[arm[-1]])
            if len(arm) == 49:
                assert len(selected) == len(used)
                other = [v ^ delta for v in arm]
                witness = arm[::-1] + [v | 256 for v in path] + other
                assert len(witness) == 193 and not defects(witness)
                return dict(reason="FOUND", witness=witness)
            sat.add_clause([-chosen[v] for v in selected])
            disconnected += 1
    return dict(reason="degree and connectivity", counts=counts, disconnected=disconnected)


if __name__ == "__main__":
    words = sorted(json.loads(Path("eight-regrow-95-29-160000000.json").read_bytes())["forms"])
    rows = []
    for index, word in enumerate(words):
        path = decode(word.encode())
        assert len(path) == 95 and not defects(path)
        result = decide(path)
        rows.append(dict(index=index, root_distance=path[-1].bit_count(), **result))
        if result["reason"] == "FOUND":
            break
    save(Path("translated-outer-arms-95.json"), dict(catalogue=len(words), rows=rows))
    print(len(rows), Counter(r["reason"] for r in rows), flush=True)
