"""All long eight-cube arms after zero or one replacement in the specified 48-set."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "254-distant-arm-partners"
SEED = "e6e522b8cb12744a1906938286731b33b0a5e5acfaff48a9e904ff3a1d14c102"
sys.path.insert(0, str(HERE.parent / "252-shorter-reference-segments"))
from replay_core import check_path, digest, word


def search(side):
    size = len(side)
    indices = {v: i for i, v in enumerate(side)}
    connectors = defaultdict(list)
    attachments = defaultdict(list)
    graph = [0] * size
    for y in range(256):
        adjacent = sorted(indices[v] for v in (y ^ (1 << axis) for axis in range(8)) if v in indices)
        if len(adjacent) == 1:
            attachments[adjacent[0]].append(y)
        if len(adjacent) == 2:
            i, j = adjacent
            connectors[i, j].append(y)
            graph[i] |= 1 << j
            graph[j] |= 1 << i

    all_vertices = (1 << size) - 1
    ends = sum(1 << i for i in attachments)
    paths = []
    nodes = 0
    def extend(order, unused, last_options):
        nonlocal nodes
        nodes += 1
        tip = order[-1]
        if not unused:
            if (1 << tip) & last_options:
                labels = [connectors[tuple(sorted(pair))] for pair in zip(order, order[1:])]
                for first, last in product(attachments[order[0]], attachments[tip]):
                    for chosen in product(*labels):
                        path = [first, side[order[0]]]
                        for i, y in zip(order[1:], chosen):
                            path.extend((y, side[i]))
                        path.append(last)
                        paths.append(tuple(min(path, path[::-1])))
            return
        choices = graph[tip] & unused
        if not choices or not last_options & unused:
            return
        # In the residual graph every unused vertex except the final endpoint
        # needs two neighbours, and the final endpoint needs at least one.
        remaining = unused
        forced_end = 0
        residual = unused | (1 << tip)
        while remaining:
            vertex = remaining & -remaining
            remaining ^= vertex
            degree = (graph[vertex.bit_length() - 1] & residual).bit_count()
            if degree >= 2:
                continue
            if degree == 0 or not vertex & last_options or forced_end:
                return
            forced_end = vertex
        if forced_end:
            last_options = forced_end
        if unused.bit_count() > 1 and last_options.bit_count() == 1:
            choices &= ~last_options
        while choices:
            bit = choices & -choices
            choices ^= bit
            order.append(bit.bit_length() - 1)
            extend(order, unused ^ bit, last_options)
            order.pop()

    for start in sorted(attachments):
        # Use the smaller first contracted vertex to fix path reversal.
        later = ends & ~((1 << (start + 1)) - 1)
        if later:
            extend([start], all_vertices ^ (1 << start), later)
    if len(paths) != len(set(paths)):
        raise ValueError("Repeated labelled arm")
    return paths, nodes


def main():
    source = PREVIOUS / "parity-families.json"
    inventory = HERE.parent / "253-repeated-segment-growth" / "closure.json"
    previous = json.loads(source.read_bytes())["shapes"]
    known = set(previous) | set(json.loads(inventory.read_bytes())["paths"])
    seed = previous[SEED]
    check_path(seed)
    base = set(seed[1::2])
    outside = [v for v in range(256) if v.bit_count() % 2 == seed[1].bit_count() % 2 and v not in base]
    if (len(base), len(outside), len(known)) != (48, 80, 241):
        raise ValueError("Unexpected source data")
    exchanges = [(None, None), *product(sorted(base), outside)]
    shapes, rows, label_rows = {}, [], []
    for removed, added in exchanges:
        side = base if removed is None else (base - {removed}) | {added}
        paths, nodes = search(sorted(side))
        ids = []
        for path in sorted(paths):
            check_path(path)
            if len(path) != 97 or set(path[1::2]) != side:
                raise ValueError("Invalid exchange")
            shape = sha256(word(path)).hexdigest()
            shapes.setdefault(shape, path)
            label_rows.append(dict(removed=removed, added=added, shape=shape, vertices=path))
            ids.append(shape)
        rows.append([removed, added, nodes, ids])
    result = dict(pins={p.name: digest(p) for p in (source, inventory, Path(__file__), Path(sys.modules["replay_core"].__file__))},
                  seed=SEED, side=sorted(base), cases=rows, paths=label_rows, shapes=shapes,
                  outside_previous=sorted(set(shapes) - known), known_shapes=len(known))
    (HERE / "arms.json").write_text(json.dumps(result, separators=(",", ":")) + "\n", encoding="utf-8", newline="\n")
    print("cases", len(rows), "positive", sum(bool(r[3]) for r in rows), "labelled", len(label_rows),
          "shapes", len(shapes), "outside inventory", len(result["outside_previous"]),
          "multiplicities", dict(Counter(len(r[3]) for r in rows)))


if __name__ == "__main__":
    main()
