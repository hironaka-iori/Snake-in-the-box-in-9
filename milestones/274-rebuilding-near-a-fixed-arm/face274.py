"""Unrestricted opposite Q8 face at every crossing of the reconstructed parents."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sys
from known274 import transfer

HERE = Path(__file__).resolve().parent


def read(path):
    return json.loads(path.read_bytes())


def save(path, data):
    temporary = path.with_suffix(".pending")
    temporary.write_bytes((json.dumps(data, separators=(",", ":")) + "\n").encode())
    temporary.replace(path)


def rooted(path):
    """Relabel the axes in first-use order and translate the start to zero."""
    axes = {}
    vertices = [0]
    steps = []
    for a, b in zip(path, path[1:]):
        bit = a ^ b
        assert bit.bit_count() == 1
        axis = axes.setdefault(bit, len(axes))
        steps.append(axis)
        vertices.append(vertices[-1] ^ (1 << axis))
    return sha256(bytes(vertices)).hexdigest(), vertices, bytes(steps)


IDENTITY = tuple(range(8))


@lru_cache(maxsize=2048)
def axis_image(axes):
    return bytes(sum(1 << axes[i] for i in range(8) if v & (1 << i)) for v in range(256))


def frame_options(path):
    flips = [(a ^ b).bit_length() - 1 for a, b in zip(path, path[1:])]
    population = [sum(bool(v & (1 << i)) for v in path[1:]) for i in range(8)]
    orders = [IDENTITY, tuple(dict.fromkeys(flips)), tuple(dict.fromkeys(flips[::-1])),
              tuple(sorted(range(8), key=lambda i:(population[i], flips.count(i), i)))]
    originals = {}
    alternatives = {}
    pairs = list(combinations(range(8), 2))
    for order in orders:
        order = tuple(order) + tuple(i for i in IDENTITY if i not in order)
        axes = tuple(order.index(i) for i in IDENTITY)
        if axes in originals:
            continue
        vertices = bytes(path[1:]).translate(axis_image(axes))
        mask = sum(1 << v for v in vertices)
        originals[axes] = mask
        alternatives.setdefault(mask, axes)
        for i, j in pairs:
            low, high, shift = swap_masks(i, j)
            swapped = (mask & ~(low | high)) | ((mask & low) << shift) | ((mask & high) >> shift)
            if swapped not in alternatives:
                alternatives[swapped] = tuple(j if t == i else i if t == j else t for t in axes)
    return originals, alternatives


@lru_cache(maxsize=28)
def swap_masks(i, j):
    shift = (1 << j) - (1 << i)
    low = sum(1 << v for v in range(256) if v & (1 << i) and not v & (1 << j))
    return low, low << shift, shift


def pack_union(roots, chunk):
    buckets = defaultdict(list)
    for k, r in roots.items():
        buckets[(r["minimum_omissions"], len(r["parent"]) - 1)].append(k)
    groups = []
    for (omissions, edges), keys in sorted(buckets.items(), key=lambda kv:(kv[0][0], -kv[0][1])):
        remaining = {k:frame_options(roots[k]["parent"]) for k in sorted(keys)}
        while remaining:
            first = next(iter(remaining))
            seed_frames, _ = remaining.pop(first)
            axes = {first:IDENTITY}
            common = seed_frames[IDENTITY]
            if remaining and chunk > 1:
                def nearest(mask):
                    best = -1
                    for _, options in remaining.values():
                        for candidate in options:
                            best = max(best, (mask & candidate).bit_count())
                        if best >= edges - 1:
                            break
                    return best
                chosen = max(seed_frames, key=lambda frame:nearest(seed_frames[frame]))
                common = seed_frames[chosen]
                axes[first] = chosen
            while remaining and len(axes) < chunk:
                winner = None
                best_score = -1
                for k, (_, options) in remaining.items():
                    for mask, frame in options.items():
                        score = (common & mask).bit_count()
                        if score > best_score:
                            best_score = score
                            winner = k, frame, mask
                    if best_score == common.bit_count():
                        break
                if len(axes) >= min(4, chunk) and best_score < edges - 12:
                    break
                k, frame, mask = winner
                del remaining[k]
                axes[k] = frame
                common &= mask
            members = sorted(axes)
            token = sha256()
            for k in members:
                token.update(bytes.fromhex(k) + bytes(axes[k]) + bytes([roots[k]["raw_endpoint"]]))
                token.update(bytes(roots[k]["parent"]))
            ident = "aligned-r%d-n%d-%s" % (omissions, edges, token.hexdigest()[:20])
            groups.append(dict(id=ident, parent_edges=edges, minimum_omissions=omissions,
                               keys=members, axes={k:list(axes[k]) for k in members},
                               blocked=[v for v in range(256) if common & (1 << v)]))
    return groups


def query_parents(group, roots):
    if "axes" in group:
        return {k:list(bytes(roots[k]["parent"]).translate(axis_image(tuple(group["axes"][k]))))
                for k in group["keys"]}
    return {k:roots[k]["parent"] for k in group["keys"]}


def make_plan(source, chunk):
    union = source.get("kind") == "rooted_union"
    roots = {}
    endpoints = {}
    for shape, item in sorted(source["shapes"].items(),
                              key=lambda kv: (kv[1]["minimum_omissions"], kv[0])):
        path = item["path"]
        if not 93 <= len(path) - 1 <= 98:
            continue
        source_name = item["source"] if union else ""
        seed = source["sources"][source_name]["seed"] if union else source["seed"]
        occupied = set(path)
        omitted = [i for i, v in enumerate(seed) if v not in occupied]
        assert omitted == item["example_omitted"] and len(omitted) == item["minimum_omissions"]
        ends = []
        words = []
        for direction, p in enumerate((path, path[::-1])):
            key, normalized, word = rooted(p)
            site = p[0]
            translated = [v ^ site for v in p]
            if key not in roots:
                roots[key] = dict(parent=translated, raw_endpoint=site, normalized=normalized,
                                  minimum_omissions=len(omitted), shape=shape, direction=direction)
            if union:
                roots[key]["source"] = source_name
            assert roots[key]["normalized"] == normalized and roots[key]["shape"] == shape
            ends.append(dict(root=key, raw_endpoint=site, direction=direction))
            words.append(word)
        assert min(words).hex() == shape
        endpoints[shape] = ends

    if union:
        return dict(roots=roots, endpoints=endpoints, groups=pack_union(roots, chunk), chunk=chunk)
    families = defaultdict(list)
    for key, r in roots.items():
        families[(r["minimum_omissions"], r["raw_endpoint"], len(r["parent"]) - 1, r.get("source", ""))].append(key)
    groups = []
    for (omissions, site, edges, source_name), keys in sorted(families.items(),
            key=lambda item: (item[0][0], -item[0][2], -len(item[1]), item[0][1])):
        keys.sort()
        for start in range(0, len(keys), chunk):
            members = keys[start:start + chunk]
            ident = "r%d-v%d-n%d-%s" % (omissions, site, edges,
                                          sha256(" ".join(members).encode()).hexdigest()[:16])
            groups.append(dict(id=ident, raw_endpoint=site, parent_edges=edges,
                               minimum_omissions=omissions, keys=members, rank=0))
    return dict(roots=roots, endpoints=endpoints, groups=groups, chunk=chunk)


def dependencies(milestones):
    sys.path.insert(0, str(milestones / "271-rebuilt-historical-partners"))
    sys.path.insert(0, str(milestones / "269-archived-93-arms"))
    import hunt
    return hunt


def row_path(folder, target, group):
    return folder / ("queries-%d" % target) / (group["id"] + ".json")


def refined_group(base, keys, roots):
    keys = sorted(keys)
    assert keys and len(set(keys)) == len(keys) and set(keys) < set(base["keys"])
    assert "axes" in base and "parent_group" not in base
    parents = query_parents(dict(keys=keys, axes=base["axes"]), roots)
    ident = sha256((base["id"] + ":" + ",".join(keys)).encode()).hexdigest()[:20]
    return dict(id="sub-" + ident, parent_group=base["id"], parent_edges=base["parent_edges"],
                minimum_omissions=base["minimum_omissions"], keys=keys,
                axes={k:base["axes"][k] for k in keys},
                blocked=sorted(set.intersection(*(set(p[1:]) for p in parents.values()))))


def check_subgroups(plan, original):
    groups = plan["groups"]
    limit = len(original)
    assert groups[:limit] == original
    bases = {g["id"]:g for g in original}
    assert len({g["id"] for g in groups}) == len(groups)
    for g in groups[limit:]:
        parent = bases[g["parent_group"]]
        assert g == refined_group(parent, g["keys"], plan["roots"])


def closed_on_disk(folder, plan, target, hunt):
    """Scheduling hint from saved locally verified queries. The audit replays these proofs."""
    groups = {g["id"]:g for g in plan["groups"]}
    closed = set()
    for directory in folder.glob("queries-*"):
        if not directory.is_dir() or int(directory.name.split("-")[1]) > target:
            continue
        cuts = defaultdict(set)
        parents = {}
        for f in directory.glob("*.json"):
            group = groups[f.stem]
            ledger = read(f)
            assert ledger["keys"] == group["keys"]
            rows = [(a,r) for a,r in ledger["rows"].items() if r.get("status") == "excluded"
                    and r.get("replay") and (folder / r["proof"]).is_file()]
            if any(tag == "0" for tag, r in rows):
                closed.update(group["keys"])
                continue
            if not rows:
                continue
            actual = query_parents(group, plan["roots"])
            for tag, _ in rows:
                path = tuple(map(int, tag.split(",")))
                for k,p in actual.items():
                    if k not in closed and set(p).isdisjoint(path[1:]):
                        cuts[k].add(path)
                        parents[k] = set(p)
        for k, branches in cuts.items():
            if k in closed:
                continue
            depth = max(map(len, branches))
            def covered(prefix):
                if tuple(prefix) in branches:
                    return True
                return len(prefix) < depth and all(covered(prefix + [v]) for v in hunt.next_sites(prefix, parents[k]))
            if covered([0]):
                closed.add(k)
    return closed


def focus(folder, plan, keys):
    original = [g for g in plan["groups"] if "parent_group" not in g]
    check_subgroups(plan, original)
    if not keys or len(set(keys)) != len(keys):
        raise ValueError("Provide distinct full rooted identifiers.")
    missing = sorted(set(keys) - plan["roots"].keys())
    if missing:
        raise ValueError("Unrecognised full rooted identifiers: " + ", ".join(missing))
    owner = {k:(i, g) for i,g in enumerate(original) for k in g["keys"]}
    assert sum(len(g["keys"]) for g in original) == len(owner) == len(plan["roots"])
    indices = {g["id"]:i for i,g in enumerate(plan["groups"])}
    selected, added = [], []
    for k in keys:
        group_number, base = owner[k]
        if len(base["keys"]) == 1:
            note = "reused original"
        else:
            singleton = refined_group(base, [k], plan["roots"])
            if singleton["id"] in indices:
                group_number = indices[singleton["id"]]
                assert plan["groups"][group_number] == singleton
                note = "reused singleton"
            else:
                group_number = len(plan["groups"])
                plan["groups"].append(singleton)
                indices[singleton["id"]] = group_number
                added.append(group_number)
                note = "appended singleton"
        selected.append(group_number)
        print(k, note, group_number, flush=True)
    check_subgroups(plan, original)
    if added:
        save(folder / "plan.json", plan)
    print("--only", *selected, flush=True)


def refine(folder, plan, args, hunt, inherited):
    original = [g for g in plan["groups"] if "parent_group" not in g]
    check_subgroups(plan, original)
    closed = closed_on_disk(folder, plan, args.target, hunt)
    closed.update(k for k, v in inherited.items() if v["maximum"] < args.target)
    indices = {g["id"]:i for i, g in enumerate(plan["groups"])}
    pending = []
    added = []
    for number, base in enumerate(original):
        if args.only and number not in args.only or base["minimum_omissions"] > args.through:
            continue
        if args.parents and base["parent_edges"] not in args.parents:
            continue
        if len(base["keys"]) < 2:
            continue
        receipt = row_path(folder, args.target, base)
        if not receipt.is_file():
            continue
        existing = read(receipt)
        assert existing["keys"] == base["keys"]
        if not any(row["status"] == "open" for row in existing["rows"].values()):
            continue
        todo = [k for k in base["keys"] if k not in closed]
        size = min(args.size, len(base["keys"]) - 1)
        masks = {k:sum(1 << v for v in p[1:]) for k,p in query_parents(base, plan["roots"]).items()}
        while todo:
            keys = [todo.pop(0)]
            if size == 2 and todo:
                other = max(todo, key=lambda k:(masks[k] & masks[keys[0]]).bit_count())
                keys.append(other)
                todo.remove(other)
            sub = refined_group(base, keys, plan["roots"])
            if sub["id"] not in indices:
                idx = len(plan["groups"])
                indices[sub["id"]] = idx
                plan["groups"].append(sub)
                added.append(idx)
            else:
                idx = indices[sub["id"]]
                assert plan["groups"][idx] == sub
            pending.append(idx)
    check_subgroups(plan, original)
    if added:
        save(folder / "plan.json", plan)
    print("Added", len(added), "groups; outstanding selected subgroup numbers:", *pending, flush=True)
    if pending:
        print("--only", *pending, flush=True)


def make_joins(parents, prefix, tail, group, roots):
    arm = prefix[:-1] + [v ^ prefix[-1] for v in tail]
    joins = {}
    aset = set(arm)
    for key, parent in parents.items():
        if set(parent) & aset == {0}:
            translated = parent[::-1] + [256 + v for v in arm]
            site = roots[key]["raw_endpoint"]
            axes = tuple(group["axes"][key]) if "axes" in group else IDENTITY
            inv = axis_image(tuple(axes.index(i) for i in IDENTITY))
            joins[key] = [(v & 256) | (inv[v & 255] ^ site) for v in translated]
    return joins


def search(folder, plan, args, hunt, inherited):
    closed = closed_on_disk(folder, plan, args.target, hunt)
    if not args.standard:
        hunt.search.base_model = hunt.deficit.model
    with TemporaryDirectory(prefix="q9-face274-") as scratch:
        tmp = Path(scratch)
        tools = None
        for number, group in enumerate(plan["groups"]):
            if args.refined_only and "parent_group" not in group:
                continue
            if group["minimum_omissions"] > args.through or args.only and number not in args.only:
                continue
            if args.parents and group["parent_edges"] not in args.parents:
                continue
            if all(k in closed or inherited.get(k, {}).get("maximum", 1000) < args.target
                   for k in group["keys"]):
                continue
            length = args.target - group["parent_edges"] - 1
            if length > 98:
                continue
            if not 1 <= length:
                raise ValueError("The solver requires a positive opposite-arm length.")
            dest = row_path(folder, args.target, group)
            dest.parent.mkdir(exist_ok=True)
            ledger = read(dest) if dest.exists() else dict(keys=group["keys"], rows={})
            assert ledger["keys"] == group["keys"]
            parents = query_parents(group, plan["roots"])
            rows = ledger["rows"]
            found = False

            def visit(prefix):
                nonlocal found, tools
                if found and args.target >= 192:
                    return
                tag = ",".join(map(str, prefix))
                old = rows.get(tag, {})
                if old.get("status") == "excluded":
                    return
                if old.get("status") == "witness" and len(prefix) > args.depth:
                    found = True
                    return
                domains = hunt.translate_domains(parents, prefix)
                if not domains:
                    return
                if len(prefix) <= args.depth:
                    for v in hunt.legal_next(prefix):
                        visit(prefix + [v])
                    return
                sites = list(domains.values())
                common = set.intersection(*sites)
                hunt.rebuild.model = hunt.family_model(sites)
                if tools is None:
                    tools = hunt.rebuild.masks.compilers(tmp)
                row = hunt.rebuild.solve(folder, tmp, tools, common, length + 1 - len(prefix),
                                         [0], old.get("cycles", []), [], args.seconds)
                if not args.standard:
                    row["encoding"] = "parity-deficit"
                if row["status"] == "witness":
                    joins = make_joins(parents, prefix, row["path"], group, plan["roots"])
                    assert joins
                    for q in joins.values():
                        assert hunt.original_audit.path_edges(q, 9) == args.target
                    row["literal_joins"] = joins
                    if args.target >= 192:
                        save(folder / ("candidate-%d.json" % args.target), joins)
                        found = True
                if tag == "0" and row["status"] == "excluded":
                    closed.update(group["keys"])
                rows[tag] = row
                save(dest, ledger)
                print(number, group["id"], len(domains), args.target, tag, row["status"], flush=True)

            visit([0])
            if found and args.target >= 192:
                return


def independently_check_domain(parents, prefix):
    tip = prefix[-1]
    sites = []
    compatible = []
    for k, p in parents.items():
        if set(prefix[1:]) & set(p):
            continue
        block = {
            v ^ tip for v in range(256)
            if v in p[1:] or (v != tip and any((v ^ w).bit_count() <= 1 for w in prefix[:-1]))
        }
        assert 0 not in block
        compatible.append(k)
        sites.append(block)
    return compatible, sites


def audit(folder, plan, data, source, hunt, inherited):
    audit = hunt.original_audit
    audit.HERE = folder
    roots = plan["roots"]
    for row in roots.values():
        assert audit.path_edges(row["parent"], 8) == len(row["parent"]) - 1
    bounds = {k:dict(minimum=len(row["parent"]), maximum=len(row["parent"]) + 98,
                     dimension_eight_maximum=len(row["parent"]) + 98, new_sat_maximum=None,
                     shape=row["shape"], parent_edges=len(row["parent"]) - 1,
                     raw_endpoint=row["raw_endpoint"], minimum_omissions=row["minimum_omissions"])
              for k, row in roots.items()}
    placements = data / (source + "-placements.json")
    if placements.exists():
        lower = read(placements)["roots"]
        assert set(lower) == set(roots)
        for k, item in lower.items():
            w = item["best"]
            assert item["parent"] == w["A"] == roots[k]["normalized"] and w["B"][0] == 0
            q = w["A"][::-1] + [256 + v for v in w["B"]]
            assert w["joined"] == q and audit.path_edges(q, 9) == w["edges"]
            assert w["pairs"] == len(q) * (len(q) - 1) // 2
            bounds[k]["minimum"] = max(bounds[k]["minimum"], w["edges"])

    group_by_id = {g["id"]:g for g in plan["groups"]}
    aligned = {}
    for group in plan["groups"]:
        if "axes" in group:
            assert set(group["axes"]) == set(group["keys"])
        else:
            assert group["rank"] == 0
        for k in group["keys"]:
            axes = group["axes"][k] if "axes" in group else list(IDENTITY)
            assert sorted(axes) == list(IDENTITY)
            coordinates = [sum(1 << axes[i] for i in range(8) if v & (1 << i)) for v in roots[k]["parent"]]
            if "parent_group" in group:
                assert coordinates == aligned[k]
            else:
                assert k not in aligned
                aligned[k] = coordinates
            assert aligned[k][0] == 0
        if "blocked" in group:
            assert set(group["blocked"]) == set.intersection(*(set(aligned[k][1:]) for k in group["keys"]))
    assert set(aligned) == set(roots)
    reports = {}
    with TemporaryDirectory(prefix="q9-audit274-") as scratch:
        tmp = Path(scratch)
        proof_files = list(folder.glob("queries-*/*.json"))
        checker = hunt.rebuild.masks.compilers(tmp)[0] if proof_files else None
        for directory in sorted({path.parent for path in proof_files}):
            target = int(directory.name.split("-")[1])
            cuts = defaultdict(set)
            counts = Counter()
            positive = set()
            for f in sorted(directory.glob("*.json")):
                group = group_by_id[f.stem]
                ledger = read(f)
                assert ledger["keys"] == group["keys"]
                parents = {k:aligned[k] for k in ledger["keys"]}
                for address, row in ledger["rows"].items():
                    prefix = [int(v) for v in address.split(",")]
                    assert prefix[0] == 0 and audit.path_edges(prefix, 8) == len(prefix) - 1
                    compatible, sites = independently_check_domain(parents, prefix)
                    assert compatible
                    length = target - group["parent_edges"] - len(prefix)
                    audit.replay(sites, length, row, tmp, checker)
                    counts[row["status"]] += 1
                    if row["status"] == "excluded":
                        for k in compatible:
                            cuts[k].add(tuple(prefix))
                    elif row["status"] == "witness":
                        tip = prefix[-1]
                        arm = prefix[:-1] + [v ^ tip for v in row["path"]]
                        expected = {k for k, p in parents.items() if set(p) & set(arm) == {0}}
                        assert expected and expected == set(row["literal_joins"])
                        for k, q in row["literal_joins"].items():
                            site = roots[k]["raw_endpoint"]
                            axes = group["axes"][k] if "axes" in group else list(IDENTITY)
                            projected = [sum(1 << axes[j] for j in range(8) if ((v & 255) ^ site) & (1 << j))
                                         | (v & 256) for v in q]
                            assert projected == parents[k][::-1] + [256 + u for u in arm]
                            assert q[:len(parents[k])] == [v ^ site for v in roots[k]["parent"][::-1]]
                            assert audit.path_edges(q, 9) == target
                            bounds[k]["minimum"] = max(bounds[k]["minimum"], target)
                            positive.add(k)
                    else:
                        assert row["status"] == "open"

            closed = []
            partial = {}
            for k, branches in cuts.items():
                depth = max(map(len, branches))
                parent = set(aligned[k])
                missing = []
                def cover(prefix):
                    if tuple(prefix) in branches:
                        return
                    if len(prefix) >= depth:
                        missing.append(prefix)
                        return
                    for v in hunt.next_sites(prefix, parent):
                        cover(prefix + [v])
                cover([0])
                if missing:
                    partial[k] = missing
                else:
                    old = bounds[k]["new_sat_maximum"]
                    bounds[k]["new_sat_maximum"] = target - 1 if old is None else min(old, target - 1)
                    bounds[k]["maximum"] = min(bounds[k]["maximum"], target - 1)
                    closed.append(k)
            assert not set(closed) & positive
            reports[str(target)] = dict(query_counts=counts, covered_roots=sorted(closed),
                                        positive_roots=sorted(positive), uncovered_prefixes=partial)
    inherited_roots = inherited["roots"]
    directly_excluded = {k for k, r in bounds.items()
                         if r["new_sat_maximum"] is not None and r["new_sat_maximum"] < 192}
    previously_excluded = {k for k, r in inherited_roots.items() if r["maximum"] < 192}
    for k, row in bounds.items():
        record = inherited_roots.get(k)
        row["inherited_maximum"] = record["maximum"] if record else None
        if record:
            row["maximum"] = min(row["maximum"], record["maximum"])
    save(folder / "inherited.json", inherited)
    aggregated = defaultdict(set)
    for ends in plan["endpoints"].values():
        for e in ends:
            aggregated[e["raw_endpoint"]].add(e["root"])
    endpoint_bounds = {}
    for v, keys in sorted(aggregated.items()):
        endpoint_bounds[v] = dict(roots=len(keys), minimum=max(bounds[k]["minimum"] for k in keys),
                                  maximum=max(bounds[k]["maximum"] for k in keys))
    assert all(v["minimum"] <= v["maximum"] for v in bounds.values())
    summary = dict(roots=bounds, by_raw_endpoint=endpoint_bounds, targets=reports,
                   source_sha256=plan["input_sha256"], inheritance="inherited.json",
                   uncovered_prefix_coordinates="aligned search frame for each root in plan.json",
                   new_sat_excluded_192=len(directly_excluded),
                   inherited_excluded_192=len(previously_excluded),
                   new_sat_only_excluded_192=len(directly_excluded - previously_excluded),
                   inherited_only_excluded_192=len(previously_excluded - directly_excluded),
                   both_excluded_192=len(directly_excluded & previously_excluded),
                   excluded_192=sum(v["maximum"] < 192 for v in bounds.values()),
                   reached_192=sum(v["minimum"] >= 192 for v in bounds.values()),
                   placements_sha256=sha256(placements.read_bytes()).hexdigest() if placements.exists() else None)
    save(folder / "summary.json", summary)
    print(source, "roots", len(roots), "excluded at 192", summary["excluded_192"],
          "reached", summary["reached_192"], flush=True)


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("action", choices=["plan", "focus", "refine", "search", "audit"])
    cli.add_argument("--source", required=True, help="prefix of SOURCE-paths.json")
    cli.add_argument("--data", type=Path, default=HERE)
    cli.add_argument("--milestones", type=Path)
    cli.add_argument("--through", type=int, default=2, choices=[0, 1, 2, 3])
    cli.add_argument("--chunk", type=int, default=96)
    cli.add_argument("--only", type=int, nargs="+", help="zero-based group numbers")
    cli.add_argument("--parents", type=int, nargs="+", help="parent lengths in edges")
    cli.add_argument("--target", type=int, default=192)
    cli.add_argument("--depth", type=int, default=0, help="number of opposite-arm prefix edges fixed")
    cli.add_argument("--seconds", type=float, default=5)
    cli.add_argument("--known", action="store_true",
                     help="skip a group if every member has a prior verified ceiling below target")
    cli.add_argument("--roots", nargs="+", help="full rooted identifiers for focus or refine")
    cli.add_argument("--size", type=int, choices=[1, 2], default=1, help="maximum subgroup size for refine")
    cli.add_argument("--refined-only", action="store_true", help="search only appended refinement groups")
    cli.add_argument("--standard", action="store_true", help="use the endpoint selector encoding")
    args = cli.parse_args()
    if args.chunk < 1 or args.depth < 0:
        cli.error("Require a positive chunk size and a nonnegative prefix depth.")
    data = args.data.resolve()
    source = data / (args.source + "-paths.json")
    folder = data / "union274" if args.source == "union" else data / "face274" / args.source
    folder.mkdir(parents=True, exist_ok=True)
    dest = folder / "plan.json"
    digest = sha256(source.read_bytes()).hexdigest()
    if args.action == "plan":
        plan = make_plan(read(source), args.chunk)
        plan["input_sha256"] = digest
        if dest.exists():
            previous = read(dest)
            if any("parent_group" in g for g in previous["groups"]):
                assert previous["input_sha256"] == digest and previous["chunk"] == args.chunk
                check_subgroups(previous, plan["groups"])
                plan["groups"] = previous["groups"]
        save(dest, plan)
        print("rooted classes", len(plan["roots"]), "groups", len(plan["groups"]),
              "groups by omissions", dict(Counter(g["minimum_omissions"] for g in plan["groups"])),
              flush=True)
        return
    plan = read(dest)
    assert plan["input_sha256"] == digest
    if args.action == "focus" or (args.action == "refine" and args.roots):
        if args.source != "union" or not args.roots:
            cli.error("focus requires --source union and --roots with full identifiers.")
        focus(folder, plan, args.roots)
        return
    if args.roots:
        cli.error("--roots applies to focus or refine.")
    milestones = args.milestones or HERE.parent
    if not (milestones / "271-rebuilt-historical-partners").is_dir():
        milestones = Path.cwd() / "milestones"
    hunt = dependencies(milestones.resolve())
    if args.action == "refine":
        if args.source != "union":
            cli.error("Refinement requires an aligned union group.")
        refine(folder, plan, args, hunt, transfer(milestones, plan["roots"])["roots"])
    elif args.action == "search":
        known = transfer(milestones, plan["roots"])["roots"] if args.known else {}
        search(folder, plan, args, hunt, known)
    else:
        independent = make_plan(read(source), plan["chunk"])
        assert all(plan[k] == v for k, v in independent.items() if k != "groups")
        check_subgroups(plan, independent["groups"])
        audit(folder, plan, data, args.source, hunt, transfer(milestones, plan["roots"]))


if __name__ == "__main__":
    main()
