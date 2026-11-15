"""Fold the mirrored arms of a 95-vertex middle and test arbitrary arms separately."""
import argparse
import json
from pathlib import Path

from bank_pivots import canonical_word
from bank_two_arms import examine
from solve import BANK, defects, save
from two_eight_layers import decode


def fold(vertex):
    return min(vertex, vertex ^ 255)


def mirror_bound(path):
    allowed = set(range(128)) - {fold(v) for v in path[1:-1]}
    graph = {v: {fold(v ^ (1 << j)) for j in range(8)} & allowed for v in allowed}
    reached = {0}
    queue = [0]
    while queue:
        new = graph[queue.pop()] - reached
        reached.update(new)
        queue.extend(new)
    sides = [[v for v in reached if v.bit_count() % 2 == parity] for parity in (0, 1)]
    counts = list(map(len, sides))
    report = dict(reachable=sorted(reached), parity=counts)
    if counts[0] < 25 or counts[1] < 24:
        return dict(**report, reason="parity capacity")
    edges = sum(len(graph[v]) for v in sides[0])
    degree_sums = []
    for side, needed in zip(sides, (25, 24)):
        removable = sorted((len(graph[v]) for v in side if v != 0), reverse=True)
        degree_sums.append(sum(removable[:len(side)-needed]))
    return dict(**report, reason="edge count", edges=edges, deletion_sums=degree_sums,
                retained_edges_at_least=edges-sum(degree_sums))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--unrestricted", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=74)
    parser.add_argument("--budget", type=int, default=400000)
    args = parser.parse_args()
    forms = json.loads(Path("eight-regrow-95-29-160000000.json").read_bytes())["forms"]
    cases = []
    for i, word in enumerate(sorted(forms)):
        path = decode(word.encode())
        if path[-1] != 255:
            continue
        assert path[0] == 0 and len(path) == 95 and not defects(path)
        bound = mirror_bound(path)
        assert bound.get("retained_edges_at_least", 49) > 48
        cases.append(dict(index=i, parent=path, mirror=bound))
    assert len(cases) == 74
    if not args.unrestricted:
        save(Path("antipodal-middle-95.json"), dict(middle_vertices=95, rows=cases))
    else:
        bank = {canonical_word(r["vertex_sequence"]) for r in json.loads(BANK.read_bytes())}
        for row in cases[args.start:args.stop]:
            tag = f"antipodal95-{row['index']}-192-{args.budget}"
            result = examine(row, tag, args.budget, None, 192)
            if result["status"] == "FOUND":
                assert not defects(result["witness"]) and canonical_word(result["witness"]) not in bank
                examine(row, tag.replace("-192-", "-193-"), args.budget, None, 193)
