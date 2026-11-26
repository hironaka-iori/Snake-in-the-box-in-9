"""Transfer stored one-crossing upper bounds by an actual isometry of Q8."""
from collections import defaultdict
from hashlib import sha256
import json


def normalize(path):
    axes = {}
    steps = []
    vertices = [0]
    for a, b in zip(path, path[1:]):
        bit = a ^ b
        assert bit.bit_count() == 1
        i = axes.setdefault(bit.bit_length() - 1, len(axes))
        steps.append(i)
        vertices.append(vertices[-1] ^ (1 << i))
    return bytes(vertices), bytes(steps), list(axes)


def isometry(actual, reference):
    """Return a literal-coordinate map after comparing every projected vertex."""
    actual_vertices, _, left = normalize(actual)
    reference_vertices, _, right = normalize(reference)
    assert actual_vertices == reference_vertices
    left += sorted(set(range(8)) - set(left))
    right += sorted(set(range(8)) - set(right))
    axes = [0] * 8
    for i, j in zip(left, right):
        axes[i] = j
    transform = [sum(1 << axes[i] for i in range(8) if x & (1 << i)) for x in range(256)]
    assert [reference[0] ^ transform[v ^ actual[0]] for v in actual] == reference
    return dict(literal_start=actual[0], reference_start=reference[0], axes=axes)


def index_interval(by_length, round_no, shape, key, path, cap):
    indexed = set()
    for reversed_reference, reference in enumerate((path, path[::-1])):
        canonical = normalize(reference)[0]
        if canonical not in indexed:
            by_length[len(path)][canonical].append((round_no, shape, key, reversed_reference, reference, cap))
            indexed.add(canonical)


def recent_intervals(load, sources, refs, old_refs, old_intervals, by_length):
    base = "273-partners-of-rebuilt-arms/"
    table = base + "containing-arms.json"
    graph_file = base + "intervals.json"
    recent = load(table)
    graph = load(graph_file)["single_extensions"]
    sources[273].update(intervals=table, interval_extensions=graph_file,
                        interval_extension_round=271, interval_rows={})
    assert not recent["outside"] and recent["complete_families"] == len(refs)
    assert recent["intervals"].keys() == refs.keys() == graph.keys()
    for shape, row in recent["intervals"].items():
        key, p, _ = min(refs[shape], key=lambda entry:entry[0])
        assert len(p) == 97 and not row["unclassified"]
        assert {bytes(entry[1]) for entry in refs[shape]} == {normalize(p)[0], normalize(p[::-1])[0]}
        children = set()
        for oriented in (p, p[::-1]):
            for axis in range(8):
                v = oriented[-1] ^ (1 << axis)
                if v in oriented or any((v ^ w).bit_count() == 1 for w in oriented[:-1]):
                    continue
                child = oriented + [v]
                children.add(min(normalize(child)[1], normalize(child[::-1])[1]).hex())
        assert children == set(graph[shape]) <= old_refs.keys()
        endpoint_caps = {r:cap for r, _, cap in refs[shape]}
        closure = {shape}
        cap = max(endpoint_caps.values())
        extension_evidence = {}
        for child in sorted(children):
            extension = old_intervals[child]
            assert len(bytes.fromhex(child)) == 97 and not extension["unclassified"]
            assert extension["ceiling"] is not None
            closure.update(extension["containing_shapes"])
            cap = max(cap, extension["ceiling"])
            extension_evidence[child] = dict(interval_maximum=extension["ceiling"],
                endpoints={r:c for r, _, c in old_refs[child]})
        assert closure == set(row["containing_shapes"]) and cap == row["ceiling"]
        sources[273]["interval_rows"][shape] = dict(endpoint_bounds=endpoint_caps,
                                                      round_271_extensions=extension_evidence)
        index_interval(by_length, 273, shape, key, p, cap)


def published_intervals(load, digests, sources, take, prior, by_length):
    short = "266-rebuilding-one-arm/"
    long = "267-fixed-arm-extensions/"
    sources[266] = dict(parents=short + "parents.json", bounds=short + "summary.json")
    sources[267] = dict(parents=long + "cases.json", bounds=long + "summary.json",
                        intervals=short + "windows.json")
    parents = load(sources[266]["parents"])["parents"]
    summary = load(sources[266]["bounds"])
    caps = {}
    for target in (192, 189):
        name = "partner-%d.json" % target
        evidence = load(short + name)
        assert digests[short + name] == summary["certificates"][name]["hash"]
        assert evidence["parents_sha256"] == digests[short + "parents.json"]
        for key, rows in evidence["roots"].items():
            receipt = rows["0"]
            if receipt["status"] == "excluded":
                assert receipt["prefix"] == [0] and receipt["replay"]
                caps[key] = min(caps.get(key, target - 1), target - 1)
                take(266, key, parents[key]["parent"], target - 1,
                     dict(file=short + name, row=[key, "0"], target=target))
    assert set(caps) == set(summary["archived_attainers"]) | set(summary["other_end_bounds"])
    assert all(caps[k] == 191 for k in summary["archived_attainers"])
    assert all(caps[k] == bounds[1] for k, bounds in summary["other_end_bounds"].items())

    data = load(sources[267]["parents"])
    long_summary = load(sources[267]["bounds"])
    covered = set(long_summary["coverage"])
    assert covered == set(data["roots"]) and not long_summary["open_192"]
    for key in covered:
        take(267, key, data["roots"][key]["parent"], 191,
             dict(file=long + "summary.json", row=["coverage", key], target=192))
    cuts = load(long + "cuts.json")
    families = load(long + "families.json")
    strengthened = load(long + "strengthened.json")
    sharper = set()
    for name, group in data["groups"].items():
        keys = group["ranks"]
        if any(len(data["roots"][key]["parent"]) != 96 for key in keys):
            continue
        facts = []
        for i, cut in enumerate(cuts[name]):
            if not cut["sites"]:
                facts.append(dict(file=long + "cuts.json", group=name, empty_cut=i))
        family = families.get(name, {})
        if not family.get("witnesses") and family.get("queries", {}).get("0", {}).get("status") == "excluded":
            facts.append(dict(file=long + "families.json", group=name, prefixes=["0"]))
        queries = strengthened.get(name, {}).get("queries", {})
        if queries:
            feasible = ["0,%d" % (1 << j) for j in range(8) if (1 << j) not in group["blocked"]]
            prefixes = ["0"] if queries.get("0", {}).get("status") == "excluded" else feasible
            if all(queries.get(tag, {}).get("status") == "excluded" for tag in prefixes):
                facts.append(dict(file=long + "strengthened.json", group=name, prefixes=prefixes))
        if facts:
            for key in keys:
                take(267, key, data["roots"][key]["parent"], 190,
                     dict(group=name, target=191, receipts=facts))
                sharper.add(key)
    assert len(sharper) == long_summary["upper_190_for_95_endpoints"]

    windows = load(sources[267]["intervals"])
    assert len(windows["seeds"]) == 5
    for k, p in windows["paths"].items():
        assert sha256(bytes(p)).hexdigest() == k
        children = set()
        for oriented in (p, p[::-1]):
            canonical = normalize(oriented)[0]
            assert any(r in (266, 267) and cap <= 191 for r, _, _, cap, _ in prior[canonical])
            for axis in range(8):
                end = oriented[-1] ^ (1 << axis)
                if end in oriented or any((end ^ u).bit_count() == 1 for u in oriented[:-1]):
                    continue
                q = oriented + [end]
                child = min(normalize(q)[0], normalize(q[::-1])[0])
                children.add(sha256(child).hexdigest())
        assert children == set(windows["successors"][k]) <= windows["paths"].keys()
    for key in windows["seeds"]:
        p = windows["paths"][key]
        assert len(p) == 95
        shape = min(normalize(p)[1], normalize(p[::-1])[1]).hex()
        index_interval(by_length, 267, shape, key, p, 191)


def transfer(milestones, roots):
    sources = {}
    digests = {}
    unavailable = []
    def load(name):
        payload = (milestones / name).read_bytes()
        digests[name] = sha256(payload).hexdigest()
        return json.loads(payload)

    prior = defaultdict(list)
    def take(round_no, key, p, cap, evidence):
        canon = normalize(p)[0]
        assert bytes(p) == canon and sha256(canon).hexdigest() == key
        prior[canon].append((round_no, key, p, cap, evidence))

    interval_refs = {}
    recent_refs = {}
    named = [
        (269, "266-rebuilding-one-arm/parents.json", "269-archived-93-arms/summary.json",
         "parents", "upper", "archive_parent_source"),
        (271, "270-optimal-seven-dimensional-arms/opposite-constructions.json",
         "271-rebuilt-historical-partners/summary.json", "roots", "maximum", "source_sha256"),
        (273, "273-partners-of-rebuilt-arms/opposite-constructions.json",
         "273-partners-of-rebuilt-arms/summary.json", "roots", "maximum", "source_sha256"),
    ]
    for round_no, parents_file, summary_file, table, capkey, pin in named:
        sources[round_no] = dict(parents=parents_file, bounds=summary_file)
        if round_no == 273 and not (milestones / summary_file).is_file():
            unavailable.append(summary_file)
            continue
        parents = load(parents_file)[table]
        summary = load(summary_file)
        assert digests[parents_file] == summary[pin]
        for key, row in summary["roots"].items():
            p = parents[key]["parent"]
            canon, word, _ = normalize(p)
            assert bytes(p) == canon and sha256(canon).hexdigest() == key
            cap = row[capkey]
            take(round_no, key, p, cap, dict(file=summary_file, row=["roots", key, capkey]))
            if round_no in (271, 273):
                shape = min(word, normalize(p[::-1])[1]).hex()
                assert shape == row["shape"] == parents[key]["shape"]
                target = interval_refs if round_no == 271 else recent_refs
                target.setdefault(shape, []).append((key, p, cap))

    interval_file = "271-rebuilt-historical-partners/intervals.json"
    sources[271]["intervals"] = interval_file
    archived = load(interval_file)
    intervals = archived["intervals"]
    assert intervals.keys() == interval_refs.keys()
    by_length = defaultdict(lambda: defaultdict(list))
    published_intervals(load, digests, sources, take, prior, by_length)
    for shape, row in intervals.items():
        cap = row["ceiling"]
        if cap is None:
            continue
        assert not row["unclassified"] and shape in row["containing_shapes"]
        todo = [shape]
        closure = {shape}
        for current in todo:
            for child in archived["single_extensions"][current]:
                if child not in closure:
                    closure.add(child)
                    todo.append(child)
        assert closure == set(row["containing_shapes"])
        assert max(entry[2] for child in closure for entry in interval_refs[child]) == cap
        key, p, _ = min(interval_refs[shape], key=lambda d:d[0])
        index_interval(by_length, 271, shape, key, p, cap)
    if recent_refs:
        recent_intervals(load, sources, recent_refs, interval_refs, intervals, by_length)

    from archival274 import archival_bound_rows, rooted_prefix_reasons
    archival_bound_rows(load, digests, sources, take, normalize)
    inherited = {}
    for k, root in roots.items():
        literal = [v ^ root["raw_endpoint"] for v in root["parent"]]
        canon = normalize(literal)[0]
        assert canon == bytes(root["normalized"]) and sha256(canon).hexdigest() == k
        reasons = []
        for round_no, key, p, cap, evidence in prior.get(canon, ()):
            reasons.append(dict(kind="same_root", round=round_no, source_root=key, ceiling=cap,
                                receipt=evidence, mapping=isometry(literal, p)))
        reasons.extend(rooted_prefix_reasons(literal, prior, normalize, isometry))
        for size, matches in by_length.items():
            for start in range(len(literal) - size + 1):
                window = literal[start:start + size]
                for found in matches.get(normalize(window)[0], ()):
                    round_no, shape, key, reversed_reference, reference, cap = found
                    reasons.append(dict(kind="certified_interval", round=round_no, shape=shape,
                                        source_root=key, reference_reversed=bool(reversed_reference),
                                        first_index=start, last_index=start + size - 1, ceiling=cap,
                                        mapping=isometry(window, reference)))
        if reasons:
            inherited[k] = dict(maximum=min(r["ceiling"] for r in reasons), reasons=reasons)
    return dict(sources=sources, sha256=digests, unavailable=unavailable, roots=inherited)
