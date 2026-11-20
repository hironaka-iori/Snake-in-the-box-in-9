"""Replay the six depth-three prefix covers using explicit vertex sets and source caps."""

from collections import defaultdict
from hashlib import sha256
from itertools import permutations
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
VERTICES = set(range(256))
NEIGHBOURS = [{v ^ (1 << a) for a in range(8)} for v in range(256)]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def placements_from_windows(path, size):
    """Axis occurrence positions identify a window up to permutation of coordinates."""
    for start in range(len(path) - size):
        occurrences = [0] * 8
        for j, (x, y) in enumerate(zip(path[start:start + size], path[start + 1:start + size + 1])):
            occurrences[(x ^ y).bit_length() - 1] |= 1 << j
        yield tuple(sorted(occurrences)), occurrences, path[start]


def image(v, axes, shift):
    for j in range(8):
        if v & (1 << j):
            shift ^= 1 << axes[j]
    return shift


def check_placements(target, sources, caps, rows, size):
    index = defaultdict(list)
    for order in (target, target[::-1]):
        for signature, axes, anchor in placements_from_windows(order, size):
            index[signature].append((axes, anchor))
    forbidden = set(target)
    candidates = {}
    for label, source in sources.items():
        maps = set()
        for signature, axes, anchor in placements_from_windows(source, size):
            for wanted, target_anchor in index.get(signature, ()):
                for free in permutations(j for j in range(8) if wanted[j] == 0):
                    unused = iter(free)
                    axes_map = tuple(wanted.index(mask) if mask else next(unused) for mask in axes)
                    maps.add((axes_map, image(anchor, axes_map, target_anchor)))
        for axes_map, shift in maps:
            placed = [image(v, axes_map, shift) for v in source]
            for end, root in enumerate((placed[0], placed[-1])):
                if root in target[1:-1]:
                    continue
                missing = frozenset(set(placed) - forbidden - {root})
                key = root, missing
                cap = caps[label, end]
                candidates[key] = min(cap, candidates.get(key, cap))
    saved = {}
    for r in rows:
        source, axes, shift = sources[r["donor"]], r["axes"], r["shift"]
        require(sorted(axes) == list(range(8)) and shift in VERTICES, "Invalid isometry")
        placed = [image(v, axes, shift) for v in source]
        root = placed[0 if r["end"] == 0 else -1]
        missing = set(placed) - forbidden - {root}
        require(root == r["root"] and sorted(missing) == r["missing"], "Placement sites disagree")
        require(r["cap"] == caps[r["donor"], r["end"]], "Incorrect archived cap")
        key = root, frozenset(missing)
        require(key not in saved, "Duplicate placement requirement")
        saved[key] = r["cap"]
    require(saved == candidates, "Complete window search or minimum caps disagree")


def replay(path, rows, entry, depth):
    root = path[0 if entry["end"] == 0 else -1]
    length = 192 - len(path)
    require((root, length) == (entry["root"], entry["partner_edges"]), "Incorrect target or root")
    expected = {i for i, r in enumerate(rows) if r["root"] == root and length > r["cap"]}
    require(sorted(expected) == entry["root_hit_requirements"], "Incorrect initial hit requirements")
    pending = [(root,)]
    proofs = set()
    leaf_totals = dict(prefix_nodes=0, dead_leaves=0, open_leaves=0)
    while pending:
        prefix = pending.pop()
        leaf_totals["prefix_nodes"] += 1
        available = VERTICES - set(path) - set(prefix)
        for x in prefix[:-1]:
            available -= NEIGHBOURS[x]
        children = NEIGHBOURS[prefix[-1]] & available
        # Only possible future sites belong to reachable. The tip itself is excluded.
        reachable = set(children)
        queue = list(children)
        while queue:
            extra = (NEIGHBOURS[queue.pop()] & available) - reachable
            reachable.update(extra)
            queue.extend(extra)
        certificates = []
        for t, x in enumerate(prefix):
            for i, r in enumerate(rows):
                if r["root"] != x or length - t <= r["cap"]:
                    continue
                owed = set(r["missing"])
                if owed.intersection(prefix[t + 1:]):
                    continue
                if len(prefix) - 1 >= t + r["cap"] + 1 or owed.isdisjoint(reachable):
                    certificates.append((t, i))
        if certificates:
            t, i = min(certificates)
            proofs.add((prefix, t, i))
        elif not children:
            leaf_totals["dead_leaves"] += 1
        elif len(prefix) == depth + 1:
            leaf_totals["open_leaves"] += 1
        else:
            pending.extend(prefix + (v,) for v in children)
    old = {(tuple(p["prefix"]), p["suffix_start"], p["placement"]) for p in entry["transfer_leaves"]}
    require(proofs == old and len(old) == len(entry["transfer_leaves"]), "Different transfer leaves")
    require(all(entry[k] == v for k, v in leaf_totals.items()), "Incorrect coverage totals")
    require(entry["excluded"] == (leaf_totals["open_leaves"] == 0), "Incorrect root status")
    return dict(root=root, **leaf_totals, transfer_leaves=len(proofs))


def main():
    frozen = HERE / "suffix-72-192-d3-w24.json"
    data = json.loads(frozen.read_bytes())
    require(data["source_sha256"] == digest(HERE / "suffix_transfer.py"), "Producer hash changed")
    require(data["arguments"] == dict(core=72, target=192, depth=3, window=24, old=None), "Wrong scope")
    inputs = {}
    for name, pin in data["inputs"].items():
        p = BASE / name
        require(digest(p) == pin, "Input hash changed: " + name)
        inputs[p.name] = json.loads(p.read_bytes())
    source = {str(r["donor_index"]): r["path"] for r in inputs["parents.json"]["rows"]}
    source.update((r["id"], r["path"]) for r in inputs["geometry.json"]["corner_closure"]["new_shapes"])
    source.update((r["id"], r["path"]) for r in inputs["cores-84.json"]["new_shapes"])
    caps = {(str(r["donor"]), r["endpoint"]): r["upper"] for r in inputs["audit.json"]["cases"]}
    for r in inputs["audit98.json"]["cases"]:
        end = [source["20"][0], source["20"][-1]].index(r["root"])
        caps["20", end] = r["partner"]["upper"]
    for filename, field in (("replay-191.json", "partner_edges"), ("extended-audit-191.json", "length")):
        for r in inputs[filename]["endpoints"]:
            if r["status"] == "excluded":
                caps[r["id"], r["end"]] = r[field] - 1
    new = {r["id"]: r["path"] for r in inputs["census-72.json"]["new_shapes"]}
    require(len(new) == len(data["records"]) == 3 and {r["id"] for r in data["records"]} == set(new),
            "Parent coverage differs")
    forced = []
    records = []
    for record in data["records"]:
        name = record["id"]
        path = new[name]
        rows = record["placements"]
        require(record["edges"] == len(path) - 1 and [r["end"] for r in record["ends"]] == [0, 1],
                "Incorrect path length or endpoints")
        check_placements(path, source, caps, rows, 24)
        ends = [replay(path, rows, end, 3) for end in record["ends"]]
        records.append(dict(id=name, placements=len(rows), ends=ends))
        if name.startswith(("460cdd57", "ff535588")):
            raw_cap = min(r["cap"] for r in rows if r["root"] == 78 and r["missing"] == [73])
            deadline = raw_cap + 1
            if deadline % 2 != (78 ^ 73).bit_count() % 2:
                deadline -= 1
            require(deadline == (91 if name.startswith("460cdd57") else 93), "Wrong visit deadline")
            for middle in (76, 79):
                prefix = (78, middle, 77)
                require(path[0] == 78 and set(prefix[1:]).isdisjoint(path)
                        and middle in NEIGHBOURS[78] & NEIGHBOURS[77] and 77 not in NEIGHBOURS[78],
                        "Illegal forced prefix")
                choices = (NEIGHBOURS[77] - set(path) - set(prefix)
                           - NEIGHBOURS[78] - NEIGHBOURS[middle])
                require(choices == {73, 93} and 73 in NEIGHBOURS[77], "Wrong fourth vertices")
                # Any later visit to 73 would be a chord to 77.
                require(any(p["prefix"] == [*prefix, 93] for p in record["ends"][0]["transfer_leaves"]),
                        "Missing rejected alternative")
                forced.append(dict(id=name, prefix=prefix, geometric_children=sorted(choices),
                                   required_vertex=73, visit_by=deadline, unique_next=73))
    require(len(forced) == 4, "Expected four forced continuations")
    out = dict(input_sha256=digest(frozen), verifier_sha256=digest(Path(__file__)),
               records=records, forced_continuations=forced)
    (HERE / "suffix-replay-72-192.json").write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    print("Verified six rooted covers and four forced continuations.")


if __name__ == "__main__":
    main()
