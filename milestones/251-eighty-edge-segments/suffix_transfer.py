"""Bound rooted partner branches by transferring a cap to a suffix of the partner."""

from argparse import ArgumentParser
from collections import defaultdict
from hashlib import sha256
from itertools import permutations
from pathlib import Path
import json


HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ALL = (1 << 256) - 1
NEIGHBOURS = [[v ^ (1 << j) for j in range(8)] for v in range(256)]
BALL = [sum(1 << u for u in [v, *NEIGHBOURS[v]]) for v in range(256)]


def load(folder, filename, pins):
    path = folder / filename
    data = path.read_bytes()
    pins[path.relative_to(BASE).as_posix()] = sha256(data).hexdigest()
    return json.loads(data)


def archive(pins):
    r248 = BASE / "248-rooted-arm-capacity"
    r249 = BASE / "249-long-parent-joins"
    r250 = BASE / "250-corner-partners"
    paths = {str(r["donor_index"]): r["path"] for r in load(r248, "parents.json", pins)["rows"]}
    caps = {(str(r["donor"]), r["endpoint"]): r["upper"] for r in load(r249, "audit.json", pins)["cases"]}
    for r in load(r249, "audit98.json", pins)["cases"]:
        end = (paths["20"][0], paths["20"][-1]).index(r["root"])
        caps["20", end] = r["joined_upper"] - len(paths["20"])
    corner = load(r249, "geometry.json", pins)["corner_closure"]["new_shapes"]
    grown = load(r250, "cores-84.json", pins)["new_shapes"]
    paths.update((r["id"], r["path"]) for r in corner + grown)
    for filename, length in (("replay-191.json", "partner_edges"), ("extended-audit-191.json", "length")):
        for r in load(r250, filename, pins)["endpoints"]:
            if r["status"] == "excluded":
                caps[r["id"], r["end"]] = r[length] - 1
    return paths, caps


def windows(path, size):
    word = bytes((x ^ y).bit_length() - 1 for x, y in zip(path, path[1:]))
    for start in range(len(word) - size + 1):
        block = word[start:start + size]
        axes = bytes(dict.fromkeys(block))
        signature = block.translate(bytes.maketrans(axes, bytes(range(len(axes)))))
        yield signature, axes, path[start]


def aligned_maps(path, anchors, size):
    """Each common ordered window specifies the images of the axes it uses."""
    found = set()
    for sig, old_axes, old_start in windows(path, size):
        for target_axes, new_start in anchors.get(sig, ()):
            unused = sorted(set(range(8)) - set(old_axes))
            unused_images = sorted(set(range(8)) - set(target_axes))
            for rest in permutations(unused_images):
                image = dict(zip(old_axes + bytes(unused), target_axes + bytes(rest)))
                axes = tuple(image[i] for i in range(8))
                shift = new_start ^ map_vertex(old_start, axes)
                found.add((axes, shift))
    return found


def map_vertex(vertex, axes):
    return sum(1 << axis for i, axis in enumerate(axes) if vertex & (1 << i))


def placements(target, paths, caps, size, own):
    anchors = defaultdict(set)
    for oriented in (target, target[::-1]):
        for sig, axes, start in windows(oriented, size):
            anchors[sig].add((axes, start))
    occupied = sum(1 << v for v in target)
    rows = {}
    for donor, path in paths.items():
        if donor == own:
            continue
        for axes, shift in aligned_maps(path, anchors, size):
            placed = [shift ^ map_vertex(v, axes) for v in path]
            mask = sum(1 << v for v in placed)
            for end, root in enumerate((placed[0], placed[-1])):
                if (donor, end) not in caps or (root in target[1:-1]):
                    continue
                missing = mask & ~(occupied | 1 << root)
                cap = caps[donor, end]
                token = root, missing
                if token not in rows or rows[token]["cap"] > cap:
                    rows[token] = dict(donor=donor, end=end, axes=list(axes), shift=shift,
                                       root=root, cap=cap, missing=missing)
    return [rows[k] for k in sorted(rows)]


def vertices(mask):
    return [i for i in range(256) if mask & (1 << i)]


def component(root, allowed):
    seen = 1 << root
    frontier = [root]
    while frontier:
        old = frontier
        frontier = []
        for x in old:
            for y in NEIGHBOURS[x]:
                bit = 1 << y
                if allowed & bit and not seen & bit:
                    seen |= bit
                    frontier.append(y)
    return seen


def cover(path, end, length, depth, rows):
    root = path[0 if end == 0 else -1]
    occupied = sum(1 << v for v in path)
    by_root = defaultdict(list)
    for i, r in enumerate(rows):
        by_root[r["root"]].append(i)
    covered, active = [], []
    open_count = dead = nodes = 0
    def visit(prefix, blocked, requirements):
        nonlocal open_count, dead, nodes
        nodes += 1
        pos = len(prefix) - 1
        tip = prefix[-1]
        bit = 1 << tip
        # A previous requirement ceases to constrain the branch once it is hit.
        live = [(i, t) for i, t in requirements if not rows[i]["missing"] & bit]
        live.extend((i, pos) for i in by_root[tip] if length - pos > rows[i]["cap"])
        allowed = ALL & ~(occupied | blocked)
        if pos == 0:
            active.extend(i for i, _ in live)
        reachable = None
        for i, t in live:
            remaining = rows[i]["missing"] & allowed
            if remaining and pos < t + rows[i]["cap"] + 1:
                if reachable is None:
                    reachable = component(tip, allowed)
                if remaining & reachable:
                    continue
            covered.append(dict(prefix=prefix, placement=i, suffix_start=t))
            return
        next_vertices = [y for y in NEIGHBOURS[tip] if allowed & (1 << y)]
        if not next_vertices:
            dead += 1
        elif pos == depth:
            open_count += 1
        else:
            for y in next_vertices:
                visit(prefix + [y], blocked | BALL[tip], live)
    visit([root], 0, [])
    return dict(end=end, root=root, partner_edges=length, prefix_nodes=nodes,
                root_hit_requirements=active, transfer_leaves=covered, dead_leaves=dead,
                open_leaves=open_count, excluded=not open_count)


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--core", type=int, required=True)
    cli.add_argument("--target", type=int, choices=(191, 192), default=192)
    cli.add_argument("--depth", type=int, choices=range(7), default=3)
    cli.add_argument("--window", type=int, choices=range(12, 73), default=24)
    cli.add_argument("--old", help="Use a specified archived donor and omit its own caps")
    args = cli.parse_args()
    pins = {}
    paths, caps = archive(pins)
    census = load(HERE, f"census-{args.core}.json", pins)
    if args.old:
        targets = {args.old: paths[args.old]}
    else:
        targets = {r["id"]: r["path"] for r in census["new_shapes"]}
    records = []
    for name, path in targets.items():
        rows = placements(path, paths, caps, args.window, name)
        ends = [cover(path, e, args.target - len(path), args.depth, rows) for e in (0, 1)]
        for r in rows:
            r["missing"] = vertices(r["missing"])
        records.append(dict(id=name, edges=len(path) - 1, placements=rows, ends=ends))
        print(name, [(r["root"], len(r["transfer_leaves"]), r["open_leaves"]) for r in ends])
    data = dict(arguments=vars(args), inputs=pins, source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                proof="Every suffix longer than the cited cap must hit a missing site by cap+1. A hit is impossible if its deadline passed or all remaining sites lie outside the current reachable component.",
                records=records)
    name = f"suffix-{args.core}-{args.target}-d{args.depth}-w{args.window}"
    if args.old:
        name += "-" + args.old.replace(":", "_")
    (HERE / (name + ".json")).write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
