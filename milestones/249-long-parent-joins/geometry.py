"""Enumerate small exceptional sets between rooted parent placements in Q8."""
from hashlib import sha256
from pathlib import Path
from collections import deque
import json


HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "248-rooted-arm-capacity"
SOURCE = HERE.parent / "246-eight-dimensional-parents"
LIMIT = 3


def load(path, inputs):
    raw = path.read_bytes()
    inputs[path.relative_to(HERE.parents[1]).as_posix()] = sha256(raw).hexdigest()
    return json.loads(raw)


def permute(v, image):
    return sum(1 << a for j, a in enumerate(image) if v & (1 << j))


def placements(vertices):
    """Apply the 8! axis permutations as transpositions of 256-bit set indicators."""
    mask = sum(1 << v for v in vertices)
    image = list(range(8))
    swaps = {}
    for a in range(8):
        for b in range(a + 1, 8):
            step = (1 << b) - (1 << a)
            lo = sum(1 << v for v in range(256) if v & (1 << a) and not v & (1 << b))
            swaps[a, b] = step, lo, lo << step

    def visit(depth, current):
        if depth == 7:
            yield current, image
            return
        yield from visit(depth + 1, current)
        for j in range(depth + 1, 8):
            a, b = sorted((image[depth], image[j]))
            step, lo, hi = swaps[a, b]
            changed = (current & ~(lo | hi)) | ((current & lo) << step) | ((current & hi) >> step)
            image[depth], image[j] = image[j], image[depth]
            yield from visit(depth + 1, changed)
            image[depth], image[j] = image[j], image[depth]

    yield from visit(0, mask)


def rooted(path, endpoint):
    root = path[0] if endpoint == 0 else path[-1]
    return {x ^ root for x in path}


def shape(path):
    transitions = [u ^ v for u, v in zip(path, path[1:])]
    def normalized(order):
        axes = {}
        return bytes(axes.setdefault(a, len(axes)) for a in order)
    return min(normalized(transitions), normalized(reversed(transitions)))


def induced(path, dimension):
    return (all(0 <= v < 1 << dimension for v in path) and len(set(path)) == len(path)
            and all(((v ^ path[j]).bit_count() == 1) == (j == i + 1)
                    for i, v in enumerate(path) for j in range(i + 1, len(path))))


def corner_closure(parents):
    """Legal corner changes commute with every cube isometry and reversal."""
    neighbours = [{v ^ (1 << i) for i in range(8)} for v in range(256)]
    old = {shape(path): i for i, path in parents.items()}
    if len(old) != len(parents):
        raise ValueError("Duplicate original shapes")
    index = old.copy()
    paths = parents.copy()
    queue = deque(sorted(parents))
    moves, new_shapes = {}, []
    while queue:
        parent = queue.popleft()
        path = paths[parent]
        sites = set(path)
        if not induced(path, 8):
            raise ValueError("Invalid 8-dimensional path")
        moves[parent] = []
        for k in range(1, len(path)-1):
            a, b, c = path[k-1:k+2]
            alternate = a ^ b ^ c
            if alternate in sites or neighbours[alternate] & sites != {a, c}:
                continue
            changed = path.copy()
            changed[k] = alternate
            code = shape(changed)
            if code not in index:
                label = f"{parent}:{k}"
                index[code], paths[label] = label, changed
                queue.append(label)
                new_shapes.append(dict(id=label, parent=parent, position=k, removed=b, inserted=alternate,
                                       endpoints=[changed[0], changed[-1]], path=changed,
                                       vertex_bytes_sha256=sha256(bytes(changed)).hexdigest(),
                                       canonical_transition_bytes_sha256=sha256(code).hexdigest()))
            moves[parent].append(dict(position=k, target=index[code]))
    # Each illustrative partner avoids both the original and changed parent.
    # Exhaust every cut on each projected word directly in Q9.
    examples = {16:(0,[1,0]), 17:(0,[3,1,0]), 19:(0,[1,0]), 99:(1,[169,233,237]),
                114:(1,[169,233,237]), 901:(1,[70,66]), 902:(1,[78,14,10,2,0])}
    for row in new_shapes:
        if row["parent"] not in examples:
            continue
        endpoint, partner = examples[row["parent"]]
        witness = dict(endpoint=endpoint, partner=partner)
        for key, name in ((row["parent"], "before"), (row["id"], "after")):
            parent = paths[key] if endpoint == 1 else paths[key][::-1]
            if parent[-1] != partner[0] or set(parent) & set(partner) != {partner[0]} or not induced(partner, 8):
                raise ValueError("Short partner has the wrong attachment")
            word = parent + partner[1:]
            legal = [k for k in range(len(word))
                     if induced(word[:k+1] + [256+v for v in word[k:]], 9)]
            if len(parent)-1 not in legal or legal != list(range(min(legal), max(legal)+1)):
                raise ValueError("Unexpected cuts on an explicit joined word")
            witness[name] = [min(legal), max(legal)]
        x, y = witness["before"], witness["after"]
        if x[1]-x[0] == y[1]-y[0]:
            raise ValueError("The asserted cardinality change is missing")
        row["short_partner_cut_example"] = witness
    return dict(initial_shapes=len(old), initial_positions=sum(len(p)-2 for p in parents.values()),
                final_shapes=len(index), moves=moves, new_shapes=new_shapes)


def main():
    inputs = {}
    parents = load(OLD / "parents.json", inputs)
    raw = load(SOURCE / "comparison.json", inputs)
    audit = load(OLD / "opposite-audit.json", inputs)
    deep = load(OLD / "deep-opposite.json", inputs)
    maximum = {r["class_id"]: r["upper"] for r in audit["classes"]}
    maximum[5] = deep["upper"]
    optimal = load(HERE.parent / "222-prefix-certificates" / "data" / "completion.json", inputs)
    p = {r["donor_index"]: r["path"] for r in parents["rows"]}
    if p[20] != raw["examples"]["optimal_98"]["path"] or not optimal["fixed_parent_93_edge_exclusion_both_roots"]:
        raise ValueError("Saved 98-edge parent or exclusion differs")
    ids = parents["remaining_96"] + parents["length_97"]
    target = {(i, e): rooted(p[i], e) for i in ids for e in (0, 1)}
    masks = {key: sum(1 << v for v in sites) for key, sites in target.items()}
    sources = []
    for e in (0, 1):
        sources.append(("donor", 20, e, rooted(p[20], e), optimal["arbitrary_compatible_partner_max_edges"]))
    for i, bound in sorted(maximum.items()):
        path = next(r["long"] for r in raw["one_crossing_pairs"] if r["seed"] == i)
        for e in (0, 1):
            sources.append(("published_class", i, e, rooted(path, e), 94 if e == 0 else bound))
    # Conditional transfers remain available when more donors are decided.
    for (i, e), sites in target.items():
        sources.append(("donor", i, e, sites, None))

    rows = []
    for kind, i, e, sites, upper in sources:
        eligible = [(k, m) for k, m in masks.items() if kind != "donor" or k != (i, e)]
        matches = {k: {} for k, _ in eligible}
        closest = {k: 257 for k, _ in eligible}
        count = 0
        for placed, image in placements(sites):
            count += 1
            for key, other in eligible:
                missing = placed & ~other
                size = missing.bit_count()
                if size < closest[key]:
                    closest[key] = size
                if size <= LIMIT and missing not in matches[key]:
                    literal = {permute(v, image) for v in sites}
                    exception = literal - target[key]
                    if sum(1 << v for v in literal) != placed or sum(1 << v for v in exception) != missing:
                        raise ValueError("Permutation or exceptional set differs")
                    matches[key][missing] = dict(vertices=sorted(exception), axes=image.copy())
        if count != 40320:
            raise ValueError("Incomplete axis permutations")
        for (j, f), records in matches.items():
            rows.append(dict(source=[kind, i, e], target=[j, f], prior_upper=upper,
                             nearest=closest[j, f], exceptions=list(records.values())))
    notes = ("A partner rooted at target zero avoiding the target parent must hit each listed set by edge "
             "prior_upper+1 if it reaches that length. With prior_upper null this implication requires an "
             "independent exclusion for the source at the desired prefix length. A witness is an image "
             "of the source's axes in rooted target coordinates. Root zero occurs in both sets.")
    corners = corner_closure(p)
    out = dict(radius=LIMIT, placements_per_source=40320, sources_sha256=inputs,
               note=notes, rows=rows, corner_closure=corners)
    (HERE / "geometry.json").write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf-8", newline="\n")
    print("Rooted source/target comparisons", len(rows))
    print("Square-flip closure", corners["initial_shapes"], corners["final_shapes"],
          [s["id"] for s in corners["new_shapes"]])
    for r in rows:
        if r["exceptions"]:
            print(r["source"], r["target"], "minimum", r["nearest"], "sets", len(r["exceptions"]))


if __name__ == "__main__":
    main()
