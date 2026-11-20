"""Recompute the Q8 core census by breadth-first growth of path isometry classes.

Cube isometries and reversal preserve the endpoints and their legal extensions.
Extending both endpoints of one representative therefore gives every next class.
Any completion can be shortened at its ends until only its original core remains.
"""

import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
INVENTORY = HERE.parent / "248-rooted-arm-capacity" / "parents.json"
GEOMETRY = HERE.parent / "249-long-parent-joins" / "geometry.json"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def verify_path(path):
    if len(set(path)) != len(path) or any(v not in range(256) for v in path):
        raise ValueError("Expected distinct vertices of Q8")
    for j, vertex in enumerate(path):
        for i in range(j):
            if ((vertex ^ path[i]).bit_count() == 1) != (i + 1 == j):
                raise ValueError(f"Incorrect induced adjacency at positions {i}, {j}")


def key(path):
    word = bytes((u ^ v).bit_length() - 1 for u, v in zip(path, path[1:]))

    def relabel(order):
        axes = bytes(dict.fromkeys(order))
        return order.translate(bytes.maketrans(axes, bytes(range(len(axes)))))

    return min(relabel(word), relabel(word[::-1]))


def next_level(level):
    following = {}
    for path in level.values():
        for oriented in (path, path[::-1]):
            end = oriented[-1]
            for axis in range(8):
                vertex = end ^ (1 << axis)
                if any((vertex ^ old).bit_count() <= 1 for old in oriented[:-1]):
                    continue
                extended = oriented + (vertex,)
                following.setdefault(key(extended), extended)
    return following


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--core", type=int, choices=(84, 88), required=True)
    core = parser.parse_args().core
    census = HERE / f"cores-{core}.json"
    saved = json.loads(census.read_bytes())
    inputs = {p.name: digest(p) for p in (INVENTORY, GEOMETRY, census, HERE / "cores.py")}
    if (saved["core_edges"] != core or saved["inventory_sha256"] != inputs[INVENTORY.name]
            or saved["geometry_sha256"] != inputs[GEOMETRY.name]
            or saved["source_sha256"] != inputs["cores.py"]):
        raise ValueError("Census and source hashes disagree")

    donors = json.loads(INVENTORY.read_bytes())["rows"]
    corners = json.loads(GEOMETRY.read_bytes())["corner_closure"]["new_shapes"]
    paths = {str(row["donor_index"]): tuple(row["path"]) for row in donors}
    paths.update((row["id"], tuple(row["path"])) for row in corners)
    for path in paths.values():
        verify_path(path)
    original = {key(path) for path in paths.values()}
    if len(original) != 22 or saved["original_classes"] != len(original):
        raise ValueError("Expected 22 distinct source shapes")

    level = {}
    windows = 0
    for path in paths.values():
        for start in range(len(path) - core):
            window = path[start:start + core + 1]
            level.setdefault(key(window), window)
            windows += 1
    archived_cores = set()
    for i, row in enumerate(saved["cores"]):
        window = tuple(row["core"])
        start = row["start"]
        if row["id"] != i or paths[row["donor"]][start:start + core + 1] != window:
            raise ValueError("Incorrect archived core provenance")
        verify_path(window)
        archived_cores.add(key(window))
    if (archived_cores != level.keys() or len(level) != len(saved["cores"])
            or saved["core_classes"] != len(level) or saved["original_provenances"] != windows):
        raise ValueError("Core sets or window counts disagree")

    found = set()
    levels = {}
    for edges in range(core, 99):
        levels[edges] = len(level)
        if edges >= 96:
            for path in level.values():
                verify_path(path)
            found.update(level)
        if edges < 98:
            level = next_level(level)

    archived_new = set()
    for row in saved["new_shapes"]:
        path = tuple(row["path"])
        verify_path(path)
        shape = key(path)
        start = row["left_edges"]
        window = tuple(saved["cores"][row["core_id"]]["core"])
        if (path[start:start + core + 1] != window or row["right_edges"] != len(shape) - core - start
                or row["edges"] != len(shape) or row["id"] != sha256(shape).hexdigest()):
            raise ValueError("Incorrect archived completion")
        archived_new.add(shape)
    new = found - original
    counts = dict(sorted(Counter(map(len, new)).items()))
    if (not original <= found or archived_new != new or len(archived_new) != len(saved["new_shapes"])
            or saved["total_classes"] != len(found)
            or counts != {int(k): v for k, v in saved["new_counts"].items()}):
        raise ValueError("Source, new, or total completion classes disagree")

    report = dict(core_edges=core, audit_sha256=digest(Path(__file__)), inputs=inputs,
                  original_classes=len(original), original_windows=windows, levels=levels,
                  total_classes=len(found), new_counts=counts,
                  new_class_ids=sorted(sha256(shape).hexdigest() for shape in new))
    output = HERE / f"core-audit-{core}.json"
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"{output.name}: {len(found)} long classes, {len(new)} new")


if __name__ == "__main__":
    main()
