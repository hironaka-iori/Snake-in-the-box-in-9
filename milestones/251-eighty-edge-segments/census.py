"""Extend all retained segments on both sides and independently enumerate by length."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "250-corner-partners"
sys.path.insert(0, str(LAST))
import core_audit as bfs
from cores import extensions
from geometry import shape


def read(path):
    return json.loads(path.read_bytes())


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--core", type=int, required=True, choices=range(68, 84))
    k = cli.parse_args().core
    refs = {str(r["donor_index"]): r["path"] for r in read(bfs.INVENTORY)["rows"]}
    refs.update({r["id"]: r["path"] for r in read(bfs.GEOMETRY)["corner_closure"]["new_shapes"]})
    legacy = {shape(p) for p in refs.values()}
    for row in read(LAST / "cores-84.json")["new_shapes"]:
        legacy.add(shape(row["path"]))
    if len(refs) != 22 or len(legacy) != 25:
        raise ValueError("Unexpected reference catalogue")
    for path in refs.values():
        bfs.verify_path(path)
    windows = {}
    for label, path in refs.items():
        for start in range(len(path)-k):
            segment = path[start:start+k+1]
            windows.setdefault(shape(segment), (segment, label, start))

    long_paths = {}
    classes = Counter()
    nodes = 0
    for segment, label, start in windows.values():
        def right(path, left_count):
            nonlocal nodes
            nodes += 1
            length = len(path)-1
            if length >= 96:
                key = shape(path)
                if key not in long_paths:
                    bfs.verify_path(path)
                    if key != bfs.key(path):
                        raise ValueError("Independent shape identifiers differ")
                    classes[length] += 1
                    long_paths[key] = dict(id=sha256(key).hexdigest(), edges=length, path=path,
                        donor=label, start=start, left=left_count, right=length-k-left_count)
            if length < 98:
                for v in extensions(path, False):
                    right(path+[v], left_count)

        def left(path, count):
            right(path, count)
            if len(path) < 99:
                for v in extensions(path, True):
                    left([v]+path, count+1)
        left(segment, 0)

    # Start independently with every labelled window, without using the DFS representatives.
    level = {}
    for path in refs.values():
        for start in range(len(path)-k):
            segment = tuple(path[start:start+k+1])
            level.setdefault(bfs.key(segment), segment)
    if level.keys() != windows.keys():
        raise ValueError("Distinct starting segments disagree")
    by_level = {}
    for length in range(k,99):
        by_level[length] = len(level)
        if length >= 96 and level.keys() != {key for key in long_paths if len(key)==length}:
            raise ValueError(f"Independent census disagrees at {length}")
        if length < 98:
            level = bfs.next_level(level)
    if not legacy <= long_paths.keys():
        raise ValueError("Missing archived classes")

    # A longer retained segment contains a k-edge segment, so all of its long
    # completions already occur here. Identify each new class's exact longest match.
    new = [long_paths[key] for key in long_paths.keys()-legacy]
    for row in new:
        row["longest_reference_segment"] = k
    for width in range(k+1,85):
        ref_shapes = {bfs.key(p[i:i+width+1]) for p in refs.values() for i in range(len(p)-width)}
        for row in new:
            p = row["path"]
            if row["longest_reference_segment"] == width-1 and any(
                    bfs.key(p[i:i+width+1]) in ref_shapes for i in range(len(p)-width)):
                row["longest_reference_segment"] = width
    if any(r["longest_reference_segment"]>=84 for r in new):
        raise ValueError("84-edge catalogue failed to cover a new representative")
    new.sort(key=lambda r:(-r["edges"], -r["longest_reference_segment"], r["id"]))
    inputs = [Path(__file__), bfs.INVENTORY, bfs.GEOMETRY, LAST/"cores-84.json",
              LAST/"core_audit.py", LAST/"cores.py", HERE.parent/"249-long-parent-joins"/"geometry.py"]
    output = dict(core=k, source_hashes={p.relative_to(HERE.parent.parent).as_posix():bfs.digest(p) for p in inputs},
                  reference_parents=len(refs), reference_occurrences=sum(len(p)-k for p in refs.values()),
                  segment_classes=len(windows), right_growth_nodes=nodes, bfs_by_length=by_level,
                  total_classes=len(long_paths), long_shapes_by_length=classes, prior_classes=len(legacy),
                  inherited_ids=sorted(sha256(key).hexdigest() for key in legacy), new_shapes=new)
    (HERE/f"census-{k}.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(k, len(windows), len(long_paths), dict(classes), "new",len(new),
          "by longest match",dict(Counter(r["longest_reference_segment"] for r in new)))


if __name__ == "__main__":
    main()
