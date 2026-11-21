"""Compare every labelled answer, then extend each retained 96-edge segment at both ends."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
from enumerate_arms import HERE, SEED, check_path, digest, word


def extensions(path):
    for reverse in (False, True):
        ordered = path[::-1] if reverse else path
        end = ordered[-1]
        for axis in range(8):
            v = end ^ (1 << axis)
            if v in ordered or any((u ^ v).bit_count() == 1 for u in ordered[:-1]):
                continue
            new = ordered + (v,)
            yield min(new, new[::-1])


def main():
    source = HERE / "arms.json"
    second = HERE / "replay-exchange.json"
    first = json.loads(source.read_bytes())
    replay = json.loads(second.read_bytes())
    if first["seed"] != replay["source_shape"] or first["side"] != replay["source_side"]:
        raise ValueError("Different starting parity sets")
    cases = {(r, a): [] for r, a, _, _ in first["cases"]}
    for row in first["paths"]:
        cases[row["removed"], row["added"]].append(row["vertices"])
    verified = {(row["removed"], row["added"]) if row["removed"] >= 0 else (None, None):
                row["paths"] for row in replay["classes"]}
    if len(cases) != 3841 or cases.keys() != verified.keys() or any(sorted(ps) != verified[k] for k, ps in cases.items()):
        raise ValueError("Independent fixed-side enumerations disagree")
    histogram = Counter()
    positive = []
    for (r, a), paths in cases.items():
        if r is not None:
            histogram[(r ^ a).bit_count()] += 1
        if paths:
            positive.append(dict(removed=r, added=a, paths=len(paths),
                                 orders=len({min(tuple(p[1::2]),tuple(p[1::2][::-1])) for p in paths})))
    seed = set(first["shapes"][SEED])
    extension_paths = {}
    exchanges = []
    for row in first["paths"]:
        path = tuple(row["vertices"])
        children = set(extensions(path))
        grandchildren = {p for child in children for p in extensions(child)}
        for p in children | grandchildren:
            check_path(p)
        extension_paths[row["shape"]] = {str(n): [dict(vertices=p, shape=sha256(word(p)).hexdigest())
                                                   for p in sorted(paths)] for n, paths in [(97,children),(98,grandchildren)]}
        exchanges.append(dict(shape=row["shape"], endpoints=[path[0], path[-1]], removed=sorted(seed-set(path)),
                              added=sorted(set(path)-seed)))
    result = dict(pins={p.name:digest(p) for p in [source,second,Path(__file__)]}, seed=SEED,
                  compared_side_sets=len(cases), compared_paths=sum(map(len,cases.values())),
                  exchanges_by_hamming_distance=histogram, positive_classes=positive,
                  vertex_differences=exchanges, longer_paths_containing_each_arm=extension_paths)
    (HERE / "geometry.json").write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8",newline="\n")
    print("All labelled paths agree.", histogram, "Longer continuations",
          {k[:8]:[len(x) for x in r.values()] for k,r in extension_paths.items()})


if __name__ == "__main__":
    main()
