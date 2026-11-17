"""Independently replay finite forced-cycle certificates; never invoke a solver."""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import sys
import time

H = Path(__file__).resolve().parents[1]
DUMMY = 512


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical_hash(value):
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def read_pinned(path, tracked, expected=None):
    path = Path(path).resolve()
    data = path.read_bytes()
    actual = digest(data)
    require(expected is None or actual == expected, f"Input hash mismatch: {path}")
    require(str(path) not in tracked or tracked[str(path)] == actual,
            f"Input changed during replay: {path}")
    tracked[str(path)] = actual
    return data


def check_pins(pins, tracked):
    require(isinstance(pins, dict), "Missing input-pin dictionary")
    for path, expected in pins.items():
        read_pinned(path, tracked, expected)


def selected_vertices(row):
    values = row["vertices"]
    require(isinstance(values, list) and len(values) == 96, "Class must contain 96 vertices")
    require(all(type(v) is int and 0 <= v < 512 for v in values), "Invalid cube vertex")
    require(len(set(values)) == 96, "Repeated selected vertex")
    parity = values[0].bit_count() % 2
    require(all(v.bit_count() % 2 == parity for v in values), "Mixed selected parities")
    return tuple(sorted(values))


def verify_candidate_descriptions(raw, tracked):
    """Rebuild equality groups without importing the producer or static auditor."""
    check_pins(raw["pins"], tracked)
    bases_path = H / "data/bases.json"
    exchange_path = H / "data/exchange.json"
    execution_path = H / "data/exchange-execution.json"
    decisions_path = H / "data/exchange-decisions.bin"
    for path in [bases_path, exchange_path, execution_path, decisions_path]:
        require(str(path.resolve()) in tracked, f"Candidate provenance omits {path.name}")
    bases = json.loads(read_pinned(bases_path, tracked))
    exchange = json.loads(read_pinned(exchange_path, tracked))
    execution = json.loads(read_pinned(execution_path, tracked))
    decisions = read_pinned(decisions_path, tracked)
    check_pins(bases["pins"], tracked)
    require(execution["status"] == "ACCEPTED_NATIVE_RESULT", "Exchange result not accepted")
    require(execution["result_sha256"] == tracked[str(exchange_path.resolve())],
            "Exchange acceptance refers to different result bytes")
    require(exchange["status"] == "COMPLETE_STATIC_COVER", "Static description inventory incomplete")
    require(exchange["source_sha256"] == tracked[str(bases_path.resolve())],
            "Exchange source differs from saved bases")
    require(exchange["decisions_sha256"] == digest(decisions), "Decision stream hash mismatch")
    require(exchange["decision_bytes"] == len(decisions), "Decision stream size mismatch")
    require(exchange["descriptions"] == len(decisions), "Description count mismatch")
    require(all(code in range(6) for code in decisions), "Unknown static decision code")

    base_rows = bases["bases"]
    base_map = {}
    for position, row in enumerate(base_rows):
        require(row["id"] == position, "Original base IDs/order changed")
        vertices = selected_vertices(row)
        parity = vertices[0].bit_count() % 2
        additions = [v for v in range(512)
                     if v.bit_count() % 2 == parity and v not in vertices]
        require(len(additions) == 160, "Wrong insertion universe")
        base_map[row["id"]] = (position, vertices, additions)
    require(len(decisions) == len(base_rows) * 96 * 160, "Wrong complete description size")

    groups = {}
    seen_descriptions = set()
    for description in exchange["candidates"]:
        require(set(description) == {"id", "base", "removed", "added"}, "Description schema changed")
        require(all(type(v) is int for v in description.values()), "Noninteger description")
        ident = description["id"]
        require(ident not in seen_descriptions, "Repeated candidate description ID")
        seen_descriptions.add(ident)
        require(description["base"] in base_map, "Unknown original base")
        position, vertices, additions = base_map[description["base"]]
        removed, added = description["removed"], description["added"]
        require(removed in vertices and added in additions, "Invalid one-vertex exchange")
        expected_id = (position * 96 + vertices.index(removed)) * 160 + additions.index(added)
        require(ident == expected_id, "Description ID does not identify its exchange")
        require(decisions[ident] == 0, "Candidate description has a noncandidate decision")
        resulting = tuple(sorted((set(vertices) - {removed}) | {added}))
        require(len(resulting) == 96, "Exchange changed class size")
        groups.setdefault(resulting, []).append(description)
    require(seen_descriptions == {i for i, code in enumerate(decisions) if code == 0},
            "Candidate descriptions do not cover exactly the saved candidate decisions")
    require(len(raw["bases"]) == len(groups), "Candidate equality-group count mismatch")
    for ident, (row, (vertices, descriptions)) in enumerate(zip(raw["bases"], groups.items())):
        require(row["id"] == ident, "Candidate class IDs/order changed")
        require(row["vertices"] == list(vertices), "Deduplicated vertices differ from exchanges")
        require(selected_vertices(row) == vertices, "Invalid deduplicated class")
        require(row["descriptions"] == descriptions, "Dedup descriptions missing, repeated, or misassigned")
    return {
        "original_classes": len(base_rows),
        "saved_description_decisions": len(decisions),
        "reconstructed_candidate_descriptions": len(seen_descriptions),
        "distinct_candidate_classes": len(groups),
        "scope": "Candidate grouping and decision-ID coverage only; noncandidate static reasons are not replayed here.",
    }


def reconstruct_graph(row):
    """Use direct Hamming comparisons, independently of the producer's XOR-neighbour sets."""
    vertices = selected_vertices(row)
    parity = vertices[0].bit_count() % 2
    adjacency = {v: set() for v in (*vertices, DUMMY)}
    ports = {}
    edge_labels = {}
    for label in range(512):
        if label.bit_count() % 2 == parity:
            continue
        neighbours = [v for v in vertices if (label ^ v).bit_count() == 1]
        if len(neighbours) == 1:
            ports.setdefault(neighbours[0], []).append(label)
        elif len(neighbours) == 2:
            v, w = neighbours
            edge_labels.setdefault((v, w), []).append(label)
            adjacency[v].add(w)
            adjacency[w].add(v)
    for v in ports:
        adjacency[v].add(DUMMY)
        adjacency[DUMMY].add(v)
    summary = {
        "vertices": list(vertices),
        "ports": [[v, labels] for v, labels in sorted(ports.items())],
        "labelled_edges": [[v, w, labels] for (v, w), labels in sorted(edge_labels.items())],
    }
    return adjacency, {
        "graph_sha256": canonical_hash(summary),
        "vertices_with_dummy": len(adjacency),
        "available_edges": sum(map(len, adjacency.values())) // 2,
        "endpoint_supported_vertices": len(ports),
        "internal_label_count": sum(map(len, edge_labels.values())),
    }


def graph_hash(adjacency):
    return canonical_hash([[v, sorted(adjacency[v])] for v in sorted(adjacency)])


def components(adjacency, allowed):
    unseen = set(allowed)
    answer = []
    while unseen:
        seed = min(unseen)
        reached = {seed}
        queue = collections.deque([seed])
        unseen.remove(seed)
        while queue:
            v = queue.popleft()
            for w in adjacency[v]:
                if w in unseen:
                    unseen.remove(w)
                    reached.add(w)
                    queue.append(w)
        answer.append(sorted(reached))
    return sorted(answer)


def verify_terminal(reason, adjacency, forced):
    kind = reason["kind"]
    if kind == "DEGREE_BELOW_TWO":
        v = reason["vertex"]
        require(v in adjacency and len(adjacency[v]) < 2, "False available-degree contradiction")
        return {"kind": kind, "vertex": v, "available_degree": len(adjacency[v])}
    if kind == "FORCED_DEGREE_ABOVE_TWO":
        v = reason["vertex"]
        require(v in forced and len(forced[v]) > 2, "False forced-degree contradiction")
        return {"kind": kind, "vertex": v, "forced_degree": len(forced[v])}
    if kind == "PROPER_FORCED_CYCLE":
        listed = reason["vertices"]
        require(isinstance(listed, list) and listed == sorted(set(listed)), "Invalid forced-cycle vertices")
        chosen = set(listed)
        require(chosen and chosen < set(adjacency), "Forced cycle must be nonempty and proper")
        require(all(len(forced[v]) == 2 and forced[v] <= chosen for v in chosen),
                "Forced-cycle degree/closure premise fails")
        require(components(forced, chosen) == [listed], "Claimed forced cycle is not connected")
        return {"kind": kind, "vertices": listed}
    if kind == "ARTICULATION":
        v = reason["vertex"]
        require(v in adjacency, "Unknown removed vertex")
        actual = components(adjacency, set(adjacency) - {v})
        claimed = reason["components"]
        require(all(isinstance(part, list) and part and part == sorted(set(part)) for part in claimed),
                "Invalid component lists")
        require(len(actual) > 1, "Vertex removal does not disconnect the remaining graph")
        require(sorted(claimed) == actual, "Claimed components differ from reconstructed components")
        return {"kind": kind, "vertex": v, "components": actual,
                "meaning": "Deleting this vertex leaves a disconnected graph; initial connectivity is unnecessary."}
    raise ValueError(f"Unknown terminal contradiction: {kind}")


def replay_row(base, row):
    require(row["id"] == base["id"], "Trace assigned to wrong candidate")
    adjacency, initial = reconstruct_graph(base)
    forced = {v: set() for v in adjacency}
    counts = collections.Counter()
    for index, step in enumerate(row["trace"]):
        require(isinstance(step, list) and len(step) == 3, f"Malformed step {index}")
        operation, v, w = step
        require(type(v) is int and type(w) is int and v in adjacency and w in adjacency and v != w,
                f"Invalid endpoints in step {index}")
        require(w in adjacency[v] and v in adjacency[w], f"Absent edge in step {index}")
        require((w in forced[v]) == (v in forced[w]), f"Asymmetric forced edge at step {index}")
        if operation == "force":
            require(len(adjacency[v]) == 2, f"Force premise fails at step {index}")
            require(w not in forced[v], f"Repeated force at step {index}")
            forced[v].add(w)
            forced[w].add(v)
        elif operation == "delete":
            require(len(forced[v]) == 2, f"Delete premise fails at step {index}")
            require(w not in forced[v] and v not in forced[w], f"Deletion of forced edge at step {index}")
            adjacency[v].remove(w)
            adjacency[w].remove(v)
        else:
            raise ValueError(f"Unknown operation at step {index}: {operation}")
        require(forced[v] <= adjacency[v] and forced[w] <= adjacency[w],
                f"Forced edge disappeared at step {index}")
        counts[operation] += 1
    require(all(forced[v] <= adjacency[v] for v in adjacency), "Final forced-edge invariant fails")
    require(all(v in adjacency[w] for v in adjacency for w in adjacency[v]), "Final adjacency asymmetric")
    require(all(v in forced[w] for v in forced for w in forced[v]), "Final forced graph asymmetric")
    if row["contradiction"] is None:
        require(row["status"] == "UNRESOLVED", "Missing contradiction for certified row")
        terminal = None
    else:
        require(row["status"] == "CERTIFICATE", "Contradiction has wrong row status")
        terminal = verify_terminal(row["contradiction"], adjacency, forced)
    return {
        "id": base["id"], "status": "VERIFIED_CONTRADICTION" if terminal else "VALID_TRACE_UNRESOLVED",
        "initial": initial, "steps": len(row["trace"]), "operations": dict(counts),
        "trace_sha256": canonical_hash(row["trace"]), "terminal": terminal,
        "final_available_sha256": graph_hash(adjacency), "final_forced_sha256": graph_hash(forced),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, default=H / "data/forced-cycles.json")
    parser.add_argument("--output", type=Path, default=H / "data/forced-replay.json")
    args = parser.parse_args()
    require(not args.output.exists(), "Refusing to replace an existing replay record")
    started = time.monotonic()
    tracked = {}
    result = {
        "status": "FAIL_REPLAY", "input_pins": tracked, "rows": [],
        "scope": "Independent finite graph and trace replay for the listed candidate minority classes only. No Lean contradiction or replay of excluded static descriptions is claimed.",
    }
    exit_code = 1
    try:
        candidates_path = H / "data/candidates.json"
        raw = json.loads(read_pinned(candidates_path, tracked))
        certificate = json.loads(read_pinned(args.certificate, tracked))
        read_pinned(Path(__file__), tracked)
        producer_path = H / "scripts/forced_cycles.py"
        read_pinned(producer_path, tracked, certificate["script_sha256"])
        require(certificate["source_sha256"] == tracked[str(candidates_path.resolve())],
                "Certificate refers to different candidate bytes")
        require(certificate["status"] == "COMPLETE_PROPAGATION", "Certificate inventory incomplete")
        result["candidate_descriptions"] = verify_candidate_descriptions(raw, tracked)
        bases = raw["bases"]
        rows = certificate["rows"]
        require(len(rows) == len(bases) == certificate["total"], "Trace coverage count mismatch")
        require([row["id"] for row in rows] == [base["id"] for base in bases],
                "Trace rows do not cover each candidate class exactly once in order")
        for base, row in zip(bases, rows):
            result["checking_class"] = base["id"]
            result["rows"].append(replay_row(base, row))
        certified = sum(row["status"] == "VERIFIED_CONTRADICTION" for row in result["rows"])
        require(certified == certificate["certified"], "Certified-row aggregate mismatch")
        for path, expected in list(tracked.items()):
            require(digest(Path(path).read_bytes()) == expected, f"Input changed before completion: {path}")
        result.update(
            status="PASS_COMPLETE_REPLAY", verified_classes=len(rows), certified_classes=certified,
            unresolved_classes=[row["id"] for row in result["rows"] if row["terminal"] is None],
            all_candidate_classes_excluded=certified == len(rows),
            terminal_counts=dict(collections.Counter(
                row["terminal"]["kind"] for row in result["rows"] if row["terminal"])),
        )
        result.pop("checking_class", None)
        exit_code = 0
    except Exception as exc:
        result["error"] = f"{type(exc).__name__}: {exc}"
    result["seconds"] = time.monotonic() - started
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x", encoding="utf-8") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
    print(json.dumps({key: result[key] for key in
                      ["status", "verified_classes", "certified_classes", "error", "seconds"]
                      if key in result}), flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
