"""Replay each closed parity-exchange neighbourhood using independent path-order enumeration."""
from collections import Counter, defaultdict, deque
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

from enumerate_arms import check_path, digest, search, word

HERE = Path(__file__).resolve().parent
R252 = HERE.parent / "252-shorter-reference-segments"
R253 = HERE.parent / "253-repeated-segment-growth"
R254 = HERE.parent / "254-distant-arm-partners"


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def shape(path):
    return sha256(word(path)).hexdigest()


def neighbourhood(side):
    base = set(side)
    free = sorted(v for v in range(256) if v not in base and (v ^ side[0]).bit_count() % 2 == 0)
    require(len(side) == len(base) == 48 and len(free) == 80, "Incorrect reference side")
    counts, paths, orders = Counter(), {}, 0
    for r, a in [(-1, -1), *product(side, free)]:
        current = base if r == -1 else base - {r} | {a}
        result, nodes = search(sorted(current))
        counts[len(result)] += 1
        orders += nodes
        for p in result:
            check_path(p)
            require(len(p) == 97 and set(p[1::2]) == current and p not in paths, "Invalid labelled completion")
            paths[p] = (r, a, shape(p))
    return paths, counts, orders


def distances(graph, starts):
    queue = deque(starts)
    result = {k: 0 for k in starts}
    while queue:
        u = queue.popleft()
        for v in graph[u]:
            if v not in result:
                result[v] = result[u] + 1
                queue.append(v)
    return result


def main():
    pins = {}
    def read(file):
        raw = file.read_bytes()
        pins[file.relative_to(HERE.parent).as_posix()] = sha256(raw).hexdigest()
        return json.loads(raw)
    for file in (Path(__file__), HERE / "enumerate_arms.py", Path(sys.modules["replay_core"].__file__)):
        pins[file.relative_to(HERE.parent).as_posix()] = digest(file)
    known_old = set(read(R253 / "closure.json")["paths"])
    parity_old = set(read(R254 / "parity-families.json")["shapes"])
    known = known_old | parity_old
    six = set(read(R253 / "relay-incidence.json")["components"]["69"]["shapes"])
    core = set(read(R252 / "census-68.json")["all_ids"])
    transports = defaultdict(set)
    for item in read(R253 / "transports.json")["results"]:
        if item["witnesses"]:
            transports[item["shape"]].add(item["end"])
    excluded = core | parity_old | {k for k, ends in transports.items() if ends == {0, 1}}
    require(len(known) == 241 and len(excluded) == 89, "Earlier inventory differs")
    cache, results = {}, {}
    for name in ("attainer", "focus"):
        data = read(HERE / (name + "-closure.json"))
        reps = data["paths"]
        require(data["closed"] and not data["pending"] and data["expanded"].keys() == reps.keys()
                and set(data["order"]) == reps.keys() and len(data["order"]) == len(reps), "Incomplete source closure")
        graph = {}
        labels_by_distance, cases_by_distance = Counter(), Counter()
        new_shape_edges_by_distance = defaultdict(set)
        source_stats = {}
        for key, p in reps.items():
            check_path(p)
            require(shape(p) == key and len(p) == 97, "Incorrect representative")
            side = tuple(sorted(p[1::2]))
            if side not in cache:
                cache[side] = neighbourhood(side)
            paths, counts, nodes = cache[side]
            expected = data["expanded"][key]
            near = {s for _, _, s in paths.values()}
            require(near == set(expected["outgoing"]) and near <= reps.keys() and key in near, "Outgoing shapes disagree")
            require(sum(counts.values()) == expected["side_classes"] == 3841
                    and expected["nonempty"] == 3841-counts[0] and len(paths) == expected["labelled"]
                    and counts == {int(k): n for k, n in expected["multiplicities"].items()}, "Side counts disagree")
            graph[key] = near
            good = set()
            for r, a, child in paths.values():
                distance = 0 if r == -1 else (r ^ a).bit_count()
                labels_by_distance[distance] += 1
                good.add((r, a, distance))
                if child != key:
                    new_shape_edges_by_distance[distance].add(tuple(sorted((key, child))))
            cases_by_distance.update(d for _, _, d in good)
            source_stats[key] = dict(successful_sides=len(good), labelled=len(paths), shapes=len(near), dfs_nodes=nodes)
        require(all(a in graph[b] for a in graph for b in graph[a]), "Reversible move gives an asymmetric edge")
        multi = distances(graph, data["seeds"])
        require(multi.keys() == reps.keys()
                and all(d == data["discovery"][k]["depth"] for k, d in multi.items()), "Distances disagree")
        for key in reps.keys()-set(data["seeds"]):
            rec = data["discovery"][key]
            parent = rec["parent"]
            source = tuple(sorted(reps[parent][1::2]))
            witness = tuple(min(reps[key], reps[key][::-1]))
            require(cache[source][0].get(witness) == (rec["removed"], rec["added"], key)
                    and multi[key] == multi[parent]+1, "Discovery witness or rank differs")
        components = []
        remaining = set(reps)
        while remaining:
            group = set(distances(graph, [min(remaining)]))
            diameter = max(max(distances(graph, [k]).values()) for k in group)
            remaining -= group
            components.append(dict(size=len(group), diameter=diameter, shapes=sorted(group)))
        outside = sorted(reps.keys()-known)
        require(outside == data["outside_previous"] and sorted(reps.keys() & six) == data["earlier_six_component"],
                "Archived shape comparison differs")
        match = reps.keys() == six
        if name == "attainer":
            require(match, "The six attained-neighbourhood shapes differ from the earlier six")
        results[name] = dict(
            shapes=len(reps), undirected_edges=sum(len(x)-1 for x in graph.values())//2,
            components=components, diameter=components[0]["diameter"] if len(components) == 1 else None,
            distance_layers=Counter(multi.values()),
            per_seed_layers={s: Counter(distances(graph, [s]).values()) for s in data["seeds"]},
            equals_round253_six=match,
            prior_excluded=sorted(reps.keys() & excluded), prior_unresolved=sorted((reps.keys() & known)-excluded),
            outside_previous=outside, successful_sides_by_distance=cases_by_distance,
            labelled_paths_by_distance=labels_by_distance,
            distinct_edges_by_exchange_distance={d:len(edges) for d, edges in sorted(new_shape_edges_by_distance.items())},
            per_source=source_stats)
        print(name, "shapes", len(reps), "components", [(x["size"], x["diameter"]) for x in components],
              "successful sides by exchange distance", dict(cases_by_distance), "outside",len(outside), flush=True)
    output = dict(pins=pins, unique_labelled_starting_sides=len(cache),
                  native_representatives=sum(r["shapes"] for r in results.values()),
                  distance_counts_scope="Per representative in its saved labelling. Distance zero keeps the side. "
                                        "An edge may be realized at more than one exchange distance.",
                  closures=results)
    (HERE / "closure-replay.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8",newline="\n")


if __name__ == "__main__":
    main()
