"""Seek 192-edge snakes by balancing the closest permitted portions of a trade."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
import sys

from seed_orbit import BANK, HERE, ROOT, WITNESS, bits, seed_classes

NEIGHBOURS = [bits(v ^ (1 << j) for j in range(9)) for v in range(512)]
SIDES = [[v for v in range(512) if v.bit_count() % 2 == parity] for parity in (0, 1)]


def signed_move(move, witness):
    perm = sum(move["blocks"], [])
    def transform(x):
        return move["translation"] ^ sum(((x >> i) & 1) << j for i, j in enumerate(perm))
    remove = sorted(map(transform, witness["negative_selection"]))
    add = sorted(map(transform, witness["positive_selection"]))
    return (add, remove) if move["reverse"] else (remove, add)


def repairs(seed, remove, add):
    deletions = [v for v in remove if seed & (1 << v)]
    insertions = [v for v in add if not seed & (1 << v)]
    used = min(len(deletions), len(insertions))
    for d in combinations(deletions, used):
        without = seed ^ bits(d)
        for a in combinations(insertions, used):
            yield without | bits(a)


def least_vertex(mask):
    return (mask & -mask).bit_length() - 1


def fixed_minority(mask, parity):
    # For a 193-vertex path both endpoints are in the opposite (majority) class.
    labels = {}
    ports = {}
    covered = 0
    for z in SIDES[1 - parity]:
        near = NEIGHBOURS[z] & mask
        count = near.bit_count()
        if count == 2:
            covered |= near
            labels[near] = z
        elif count == 1:
            ports[least_vertex(near)] = z
    if covered != mask:
        return "isolated", least_vertex(mask ^ covered)
    if len(ports) < 2:
        return "fewer_than_two_endpoints", sorted(ports)
    adj = {v: set() for v in SIDES[parity] if mask & (1 << v)}
    for edge in labels:
        u, v = least_vertex(edge), edge.bit_length() - 1
        adj[u].add(v)
        adj[v].add(u)
    leaves = [v for v, ns in adj.items() if len(ns) == 1]
    if len(leaves) > 2 or any(v not in ports for v in leaves):
        return "forced_ends", leaves
    root = next(iter(adj))
    seen = {root}
    stack = [root]
    while stack:
        unseen = adj[stack.pop()] - seen
        seen.update(unseen)
        stack.extend(unseen)
    if len(seen) < 96:
        return "disconnected", len(seen)
    sys.path.insert(0, str(ROOT / "work/solver_packages"))
    from ortools.sat.python import cp_model
    model = cp_model.CpModel()
    vertices = list(adj)
    index = {v: i for i, v in enumerate(vertices)}
    directed = [(index[u], index[v]) for u in vertices for v in adj[u]]
    for v in ports:
        directed.extend([(96, index[v]), (index[v], 96)])
    arcs = [(i, j, model.new_bool_var(f"a{i}_{j}")) for i, j in directed]
    model.add_circuit(arcs)
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.max_time_in_seconds = 1.0
    status = solver.solve(model)
    if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return solver.status_name(status), None
    succ = {i: j for i, j, var in arcs if solver.value(var)}
    order = []
    i = succ[96]
    while i != 96:
        if len(order) >= 96:
            raise ValueError("Invalid contracted circuit")
        order.append(vertices[i])
        i = succ[i]
    path = [ports[order[0]], order[0]]
    for u, v in zip(order, order[1:]):
        path.extend((labels[(1 << u) | (1 << v)], v))
    path.append(ports[order[-1]])
    if len(set(path)) != 193 or len(path) != 193 or any(
            ((v ^ path[j]).bit_count() == 1) != (j == i + 1)
            for i, v in enumerate(path) for j in range(i + 1, len(path))):
        raise ValueError("Candidate failed direct verification")
    return "192_edges", path


def main():
    orbit_file = HERE / "seed-orbit.json"
    orbit = json.loads(orbit_file.read_bytes())
    witness = json.loads(WITNESS.read_bytes())
    classes = seed_classes()
    nearest = min(c["minimum"] for c in orbit["classes"])
    seen = set()
    outcomes = Counter()
    totals = Counter()
    examples = {}
    for row in orbit["classes"]:
        if row["minimum"] != nearest:
            continue
        parity = row["parity"]
        seed, = [s for s, ids in classes[parity].items() if ids == row["seed_ids"]]
        for move in row["closest"]:
            remove, add = signed_move(move, witness)
            for candidate in repairs(seed, remove, add):
                totals["descriptions"] += 1
                if candidate in seen:
                    continue
                seen.add(candidate)
                if candidate.bit_count() != 96:
                    raise ValueError("Unbalanced repair")
                status, data = fixed_minority(candidate, parity)
                outcomes[status] += 1
                if status not in examples:
                    examples[status] = dict(seed_ids=row["seed_ids"], move=move,
                                            vertices=[v for v in SIDES[parity] if candidate & (1 << v)],
                                            evidence=data)
                if status == "192_edges":
                    break
            if "192_edges" in outcomes:
                break
        if "192_edges" in outcomes:
            break
    result = dict(closest_mismatches=nearest, descriptions=totals["descriptions"], distinct=len(seen),
                  outcomes=outcomes, examples=examples, source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  orbit_sha256=sha256(orbit_file.read_bytes()).hexdigest(), bank_sha256=sha256(BANK.read_bytes()).hexdigest())
    (HERE / "repair-search.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(result["descriptions"], result["distinct"], dict(outcomes))


if __name__ == "__main__":
    main()
