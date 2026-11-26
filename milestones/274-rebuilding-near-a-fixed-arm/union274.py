"""Search the union of the seed neighbourhoods once, then transport the verified results."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
from pathlib import Path

from face274 import make_plan, read, rooted, save
from known274 import isometry

HERE = Path(__file__).resolve().parent


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def build(data, names):
    if names is None:
        names = sorted(p.name[:-11] for p in data.glob("*-paths.json") if p.name != "union-paths.json")
    if not names or "union" in names or len(set(names)) != len(names):
        raise ValueError("Select distinct, real seed names.")
    sources = {}
    appearances = defaultdict(dict)
    candidates = defaultdict(list)
    for name in sorted(names):
        filename = data / (name + "-paths.json")
        actual = read(filename)
        sources[name] = dict(seed=actual["seed"], sha256=digest(filename))
        for shape, record in actual["shapes"].items():
            path = record["path"]
            if not 93 <= len(path) - 1 <= 98:
                continue
            appearances[shape][name] = dict(minimum_omissions=record["minimum_omissions"],
                example_omitted=record["example_omitted"], placements=record["placements"],
                literal_sha256=sha256(bytes(path)).hexdigest())
            candidates[shape].append((record["minimum_omissions"], name, record))
    shapes = {}
    for shape in sorted(candidates):
        count, name, representative = min(candidates[shape], key=lambda t:(t[0], t[1]))
        shapes[shape] = dict(path=representative["path"], source=name, minimum_omissions=count,
            example_omitted=representative["example_omitted"],
            placements=sum(t["placements"] for t in appearances[shape].values()),
            appearances=appearances[shape])
    out = dict(kind="rooted_union", minimum=93, maximum=98, sources=sources, shapes=shapes)
    save(data / "union-paths.json", out)
    print("Union of", len(names), "seeds:", len(shapes), "distinct Q8 shapes", flush=True)


def check_path(p, dimension):
    rank = {v:i for i, v in enumerate(p)}
    assert len(rank) == len(p) and all(0 <= v < 1 << dimension for v in p)
    for i, v in enumerate(p):
        neighbours = {rank[v ^ (1 << j)] for j in range(dimension) if v ^ (1 << j) in rank}
        expected = {h for h in (i - 1, i + 1) if 0 <= h < len(p)}
        assert neighbours == expected
    return len(p) * (len(p) - 1) // 2


def literal(row):
    return [v ^ row["raw_endpoint"] for v in row["parent"]]


def transform(path, mapping):
    axes = mapping["axes"]
    assert sorted(axes) == list(range(8))
    lookup = [sum(1 << axes[i] for i in range(8) if u & (1 << i)) for u in range(256)]
    return [(v & 256) | (mapping["reference_start"] ^ lookup[(v & 255) ^ mapping["literal_start"]])
            for v in path]


def make_witness(A, path):
    assert path[:len(A)] == A[::-1] and path[len(A)] == 256 and all(v >= 256 for v in path[len(A):])
    pairs = check_path(path, 9)
    return dict(A=A, B=[v - 256 for v in path[len(A):]], joined=path, pairs=pairs, edges=len(path) - 1)


def union_witnesses(folder, plan, placement, report):
    best = {}
    for k, row in placement["roots"].items():
        p = plan["roots"][k]["normalized"]
        assert p == row["parent"] and make_witness(p, row["best"]["joined"]) == row["best"]
        best[k] = (row["best"], "union-placements.json")
    for file in sorted(folder.glob("queries-*/*.json")):
        for address, row in read(file)["rows"].items():
            for k, path in row.get("literal_joins", {}).items():
                if len(path) - 1 <= best[k][0]["edges"]:
                    continue
                arm = plan["roots"][k]
                assert path[:len(arm["parent"])] == literal(arm)[::-1]
                mapped = transform(path, isometry(literal(arm), arm["normalized"]))
                best[k] = (make_witness(arm["normalized"], mapped),
                           "union274/" + file.relative_to(folder).as_posix() + "#" + address)
    for k, result in best.items():
        assert result[0]["edges"] == report["roots"][k]["minimum"]
    return best


def statistics(keys, bounds):
    keys = set(keys)
    return dict(root_count=len(keys), roots=sorted(keys),
                excluded_192=sum(bounds[k]["maximum"] < 192 for k in keys),
                reaches_192=sum(bounds[k]["minimum"] >= 192 for k in keys),
                minimum=max((bounds[k]["minimum"] for k in keys), default=None),
                maximum=max((bounds[k]["maximum"] for k in keys), default=None))


def slice_all(data):
    united = data / "union-paths.json"
    union = read(united)
    folder = data / "union274"
    plan = read(folder / "plan.json")
    audit = read(folder / "summary.json")
    placement_file = data / "union-placements.json"
    placed = read(placement_file)
    assert plan["input_sha256"] == audit["source_sha256"] == digest(united)
    assert audit["placements_sha256"] == digest(placement_file)
    assert set(plan["roots"]) == set(audit["roots"]) == set(placed["roots"])
    best = union_witnesses(folder, plan, placed, audit)
    named = ["union-paths.json", "union274/plan.json", "union274/summary.json",
             "union274/inherited.json", "union-placements.json"]
    reference = {name:digest(data / name) for name in named}
    membership = defaultdict(set)
    for shape, row in union["shapes"].items():
        for e in plan["endpoints"][shape]:
            membership[e["root"]].update(row["appearances"])
    projected = {}
    for name, source in union["sources"].items():
        infile = data / (name + "-paths.json")
        assert source["sha256"] == digest(infile)
        catalogue = read(infile)
        assert catalogue["seed"] == source["seed"]
        local = make_plan(catalogue, plan["chunk"])
        local["input_sha256"] = source["sha256"]
        roots = local["roots"]
        assert set(roots) == {k for k, names in membership.items() if name in names}
        bounds = {}
        maps = {}
        donor_rows = {}
        for k, local_row in roots.items():
            u = plan["roots"][k]
            arm = literal(local_row)
            uarm = literal(u)
            normalized = local_row["normalized"]
            assert normalized == u["normalized"] and bytes(normalized) == bytes(placed["roots"][k]["parent"])
            assert rooted(arm)[0] == k and check_path(arm, 8)
            mapping = isometry(arm, uarm)
            assert transform(arm, mapping) == uarm
            maps[k] = mapping
            witness, origin = best[k]
            to_local = isometry(normalized, arm)
            literal_join = transform(witness["joined"], to_local)
            assert literal_join[:len(arm)] == arm[::-1] and literal_join[len(arm)] == (256 | arm[0])
            assert check_path(literal_join, 9) == witness["pairs"]
            record = dict(placed["roots"][k])
            if origin != "union-placements.json":
                record["donor_best"] = record["best"]
            record.update(best=witness, best_source=origin, literal_join=literal_join)
            donor_rows[k] = record
            bounds[k] = dict(audit["roots"][k], raw_endpoint=local_row["raw_endpoint"],
                             minimum_omissions=local_row["minimum_omissions"],
                             union_minimum_omissions=u["minimum_omissions"])
            assert bounds[k]["minimum"] == witness["edges"] <= bounds[k]["maximum"]
        levels = {}
        for r, level in catalogue["levels"].items():
            n = int(r)
            first = {k for k, row in roots.items() if row["minimum_omissions"] == n}
            cumulative = {k for k, row in roots.items() if row["minimum_omissions"] <= n}
            levels[r] = dict(first_appearing=statistics(first, bounds), at_most=statistics(cumulative, bounds),
                labelled_paths_by_edges_at_exact_omissions=level["histogram"],
                roots_also_in_other_seed_families=sum(len(membership[k]) > 1 for k in cumulative))
        by_site = defaultdict(set)
        for ends in local["endpoints"].values():
            for end in ends:
                by_site[end["raw_endpoint"]].add(end["root"])
        direct = {k for k,r in bounds.items() if r["new_sat_maximum"] is not None and r["new_sat_maximum"] < 192}
        inherited = {k for k,r in bounds.items() if r["inherited_maximum"] is not None and r["inherited_maximum"] < 192}
        targets = {t:dict(covered_roots=sorted(set(c["covered_roots"]) & roots.keys()),
                          positive_roots=sorted(set(c["positive_roots"]) & roots.keys()))
                   for t,c in audit["targets"].items()}
        summary = dict(roots=bounds, source_sha256=source["sha256"], union_evidence=reference,
                union_root_coordinate_maps=maps, omission_budgets=levels, targets=targets,
                by_raw_endpoint={v:dict(roots=len(keys),minimum=max(bounds[k]["minimum"] for k in keys),
                    maximum=max(bounds[k]["maximum"] for k in keys)) for v,keys in by_site.items()},
                new_sat_excluded_192=len(direct), inherited_excluded_192=len(inherited),
                new_sat_only_excluded_192=len(direct - inherited), inherited_only_excluded_192=len(inherited - direct),
                both_excluded_192=len(direct & inherited),
                excluded_192=sum(r["maximum"] < 192 for r in bounds.values()),
                reached_192=sum(r["minimum"] >= 192 for r in bounds.values()))
        projection = {k:v for k,v in placed.items() if k not in ("roots", "fixed_roots", "best")}
        projection.update(roots=donor_rows, fixed_roots=len(roots), best=max((w["best"]["edges"] for w in donor_rows.values()),
                          default=None), source_sha256=source["sha256"], union_placement_sha256=reference["union-placements.json"])
        dest = data / (name + "-placements.json")
        save(dest, projection)
        summary["placements_sha256"] = digest(dest)
        target = data / "face274" / name
        target.mkdir(exist_ok=True, parents=True)
        save(target / "plan.json", local)
        save(target / "summary.json", summary)
        projected[name] = dict(roots=len(roots), shapes=len(local["endpoints"]), by_budget=levels)
        print(name, len(roots), "roots,", summary["excluded_192"], "exclude 192", flush=True)
    assert set(membership) == set(plan["roots"])
    save(folder / "slices.json", dict(sources=projected, union_references=reference,
        roots_by_number_of_seed_families=Counter(len(v) for v in membership.values()),
        distinct_roots=len(membership), source_root_incidents=sum(map(len, membership.values()))))


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["build", "slice"])
    parser.add_argument("--data", type=Path, default=HERE)
    parser.add_argument("--sources", nargs="+", help="actual seed names for building the union")
    args = parser.parse_args()
    if args.action == "build":
        build(args.data.resolve(), args.sources)
    else:
        slice_all(args.data.resolve())
