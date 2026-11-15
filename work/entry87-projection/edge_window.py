"""Check the edge-incidence reduction for 117 or more occupied eight-cube vertices."""
import argparse
from collections import Counter
from functools import lru_cache
import gzip
import json
from pathlib import Path

from dense_face_catalogue import list_classes
from edge_rich_faces import read_shapes
from facet_hole_labels import hole_labels
from facet_resolution import verify_resolution
from forest_orbit_weights import bound
from variable_facet_weights import solve as template_bound
from solve import save


@lru_cache(None)
def read(name):
    file = Path(name)
    return json.loads(file.read_bytes()) if file.exists() else None


def check(size, target, replay, packed, mode, checker=None):
    labels = hole_labels()
    archive = {}
    sealed = packed is not None and packed.exists()
    if sealed:
        with gzip.open(packed, "rt", encoding="utf-8") as stream:
            archive = dict(json.loads(line) for line in stream)
    used = {}
    counts = Counter()
    open_cases = []
    checked = set()
    resolutions = []

    def proof(name):
        return archive.get(name) if sealed else read(name)

    def accept(name, record, test):
        if replay and name not in checked:
            assert test() == record
            checked.add(name)
        used[name] = record

    def fixed(n, i, vertices):
        prefix = "forest-role-weight" if n >= 62 else "individual-weight"
        name = f"{prefix}-{n}-{i}.json"
        r = proof(name)
        if r is not None:
            assert (r["fixed"], r["size"]) == (vertices, 117)
            cert = r["certificate"]
            numer = r["numerator"] + (size-117)*cert["per_vertex"]
            if numer // cert["scale"] < target:
                accept(name, r, lambda: bound(set(vertices), 117, cert))
                counts["fixed integer inequalities"] += 1
                return True
        prefix = ("individual-facet" if n == 61 else "edge-rich") if size == 117 else f"population{size}"
        for file in sorted(Path(".").glob(f"{prefix}-{n}-{i}-*-checked.json")):
            receipt = read(file.name)
            if receipt["status"] != "UNSAT" or receipt["component_limit"] < size-target:
                continue
            assert receipt["fixed"] == vertices and receipt["size"] == size
            assert "s VERIFIED" in receipt["checker"]
            if replay or checker:
                verify_resolution(file, vertices, size, size-target, checker)
            resolutions.append(file.name)
            counts["resolution"] += 1
            return True
        return False

    def template(n, base, i):
        prefix = "variable-facet" if base == 64 else "variable-mark-63"
        name = f"{prefix}-{i}-61-3.json"
        r = proof(name)
        if r is None:
            return False
        assert (r["template"], r["lower_size"], r["upper_size"], r.get("base_size",64)) == (i,61,56,base)
        assert 61 <= n <= base
        cert = r["certificate"]
        numer = r["numerator"] + (n-61)*cert["lower"] + (size-n-56)*cert["upper"]
        if numer // cert["scale"] >= target:
            return False
        def replay_template():
            verified = template_bound(i, 61, 3, cert, base)
            if base != 64:
                verified["base_size"] = base
            return verified
        accept(name, r, replay_template)
        counts[f"{base}-vertex template"] += 1
        return True

    rows61 = list_classes(61, True)
    deletions = read("seven-deletion-classes.json")
    previous = read("dense-facet-audit.json")
    for n in range(61, 65):
        rows = rows61 if n == 61 else deletions[str(n)]
        if n >= 62 and size == 117 and target >= 104:
            assert previous[str(n)]["excluded"] == previous[str(n)]["classes"] == len(rows)
            counts["previous 62-64 proof"] += len(rows)
            continue
        for i, r in enumerate(rows):
            group = r["full_class"]
            if group >= 0 and template(n, 64, group):
                continue
            if group >= 0 and n <= 63:
                original = sum(1 << v for v in r["forest"])
                parent = r["parent_mask"] if n == 61 else original | sum(1 << v for v in r["deleted"])
                if any(template(n, 63, key) for key, sites in labels[parent] if sites & (parent ^ original)):
                    continue
            if not fixed(n, i, r["forest"]):
                open_cases.append((n, i))

    # After the dense faces have been excluded, all populations lie in
    # [size-60,60]. Seven edges incidences per eight-cube edge force one
    # face above the all-faces threshold, or one denser face above the
    # dense-faces threshold when each opposite face has at most 48 edges.
    if size <= 120 and mode != "facets":
        if mode == "dense":
            assert size-60 >= 57
            minimum = (7*target+7)//8 - 48
            low = (size+1)//2
        else:
            minimum = (7*target+15)//16
            low = size-60
        assert low >= 56
        for n in range(low, 61):
            for i, vertices, edges in read_shapes(n, minimum):
                if not fixed(n, i, vertices):
                    open_cases.append((n, i))
    else:
        minimum, low = None, None
    record = dict(size=size, excluded_edge_target=target, choice=mode,
                  scope="faces of population at least 61" if mode=="facets" else "all forests",
                  minimum_face_edges=minimum,
                  minimum_face_population=low, methods=dict(counts), resolution_receipts=resolutions,
                  open_cases=open_cases)
    if packed and not open_cases and not packed.exists():
        with packed.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as output:
            for name, r in sorted(used.items()):
                output.write(json.dumps([name,r],separators=(",",":")).encode()+b"\n")
    return record


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("size", type=int, choices=range(116,129))
    parser.add_argument("target", type=int, choices=range(103,111))
    parser.add_argument("--choice", choices=("dense","all","facets"), default="dense")
    parser.add_argument("--archive", type=Path)
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--checker", type=Path)
    a = parser.parse_args()
    record = check(a.size, a.target, a.replay, a.archive, a.choice,
                   a.checker.resolve() if a.checker else None)
    path = Path(f"edge-window-{a.size}-{a.target}-{a.choice}.json")
    save(path,record)
    print(record["methods"],len(record["open_cases"]),record["open_cases"][:12])
