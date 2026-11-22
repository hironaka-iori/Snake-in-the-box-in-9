"""Enumerate the complete radius-two shell about a labelled attaining Q8 parent."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from math import comb
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "255-parity-exchange-arms"))
from enumerate_arms import check_path, digest, search, word

NEIGH = [sum(1 << (x ^ (1 << j)) for j in range(8)) for x in range(256)]
PARENTS = MS / "248-rooted-arm-capacity/endpoint94.json"
PARTNERS = MS / "248-rooted-arm-capacity/attainers.json"


def read(path):
    return json.loads(path.read_bytes())


def mask(vertices):
    return sum(1 << v for v in vertices)


def viable(sites, removals, outside):
    """Screen by exact supply of usable opposite neighbours of every member."""
    retained = sorted(sites - set(removals))
    fixed = mask(retained)
    degrees = [(fixed & nb).bit_count() for nb in NEIGH]
    one = mask(y for y, d in enumerate(degrees) if d == 1)
    zero = mask(y for y, d in enumerate(degrees) if d == 0)
    two = mask(y for y, d in enumerate(degrees) if d == 2)
    # Each insertion itself needs two usable physical neighbours.
    candidates = [a for a in outside if (NEIGH[a] & (zero | one)).bit_count() >= 2]
    for i, a in enumerate(candidates):
        n = NEIGH[a]
        ones = (one & ~n) | (zero & n)
        twos = (two & ~n) | (one & n)
        usable = ones | twos
        selected = retained + [a]
        # A label's degree in the class increases with each insertion.
        if any((NEIGH[v] & usable).bit_count() < 2 for v in selected):
            continue
        empty = zero & ~n
        for b in candidates[i+1:]:
            nb = NEIGH[b]
            if (nb & (empty | ones)).bit_count() < 2:
                continue
            singles = (ones & ~nb) | (empty & nb)
            if singles.bit_count() < 2:
                continue
            kept_usable = usable & ~(nb & twos)
            if all((NEIGH[v] & kept_usable).bit_count() >= 2 for v in selected):
                yield a, b


def main():
    class_id = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    component_file = MS / "255-parity-exchange-arms/attainer-closure.json"
    component = read(component_file)
    if class_id == -1:
        key, = set(component["paths"]) - set(component["seeds"])
        seed = component["paths"][key]
    else:
        seed, = [r["rooted_parent"] for r in read(PARENTS)["records"] if r["case"] == [class_id, 0]]
        record, = [r for r in read(PARTNERS)["records"] if r["class_id"] == class_id]
        if not any(len(row["path"]) == 95 and set(row["path"]) & set(seed) == {0} for row in record["paths"]):
            raise ValueError("Reference arm must attain a 191-edge join at zero")
    check_path(seed)
    if len(seed) != 97 or sha256(word(seed)).hexdigest() not in component["paths"]:
        raise ValueError("Reference is outside the six-shape component")
    side = set(seed[1::2])
    outside = [v for v in range(256) if (v ^ seed[1]).bit_count() % 2 == 0 and v not in side]
    known_sources = [(MS / "253-repeated-segment-growth/closure.json","paths"),
                     (MS / "254-distant-arm-partners/parity-families.json","shapes"),
                     (MS / "255-parity-exchange-arms/focus-closure.json","paths")]
    known = set().union(*(read(p)[k] for p,k in known_sources))
    if (len(side),len(outside),len(known)) != (48,80,264):
        raise ValueError("Unexpected input dimensions")
    rows, positives, shapes = [], [], {}
    for removed in combinations(sorted(side), 2):
        survivors, success, labelled = 0, 0, 0
        for inserted in viable(side, removed, outside):
            survivors += 1
            target = (side - set(removed)) | set(inserted)
            paths, _ = search(sorted(target))
            if paths:
                success += 1
                labelled += len(paths)
                records = []
                for path in sorted(paths):
                    check_path(path)
                    if len(path) != 97 or target != set(path[1::2]):
                        raise ValueError("Incorrect reconstructed path")
                    key = sha256(word(path)).hexdigest()
                    shapes.setdefault(key, path)
                    records.append(dict(shape=key, vertices=path))
                positives.append(dict(removed=removed,inserted=inserted,paths=records))
        rows.append([*removed,survivors,success,labelled])
    counts=dict(removed_pairs=len(rows),all_classes=len(rows)*comb(80,2),
                pass_supply=sum(r[2] for r in rows),viable_classes=len(positives),
                labelled=sum(r[4] for r in rows),shapes=len(shapes),new_shapes=len(set(shapes)-known))
    data=dict(class_id=class_id,reference=seed,reference_shape=sha256(word(seed)).hexdigest(),
              counts=counts, baseline_shapes=len(known),new_shapes=sorted(set(shapes)-known),
              per_removed_pair=rows,positive_classes=positives,shapes=shapes,
              sha256={p.relative_to(MS).as_posix():digest(p) for p in
                      [PARENTS,PARTNERS,component_file,*(p for p,k in known_sources),Path(__file__),
                       Path(sys.modules["enumerate_arms"].__file__),Path(sys.modules["replay_core"].__file__)]})
    destination=HERE / ("shell-"+str(class_id)+".json")
    destination.write_text(json.dumps(data,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print(class_id,counts,flush=True)


if __name__ == "__main__":
    main()
