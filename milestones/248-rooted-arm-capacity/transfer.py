"""Compare the reachable continuations of all 70 first steps under rooted Q8 isometries."""
from collections import Counter
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import sys


HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "247-relative-middle-placements"
sys.path.insert(0, str(PREVIOUS))
import partner


AXES = tuple(range(8))
AXIS_MAPS = factorial(len(AXES))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_evidence(name, pins):
    raw = (PREVIOUS / name).read_bytes()
    pins[name] = sha256(raw).hexdigest()
    return json.loads(raw)


def checked_queries(ledger, receipt, ledger_hash):
    require(receipt["source_sha256"] == ledger_hash, "LRAT receipt does not match its ledger")
    key = lambda r: (r["class_id"], r["endpoint"], tuple(r["prefix"]))
    cases = {key(r): r for r in receipt["cases"]}
    require(len(cases) == len(receipt["cases"]) == receipt["verified"], "Duplicated proof receipt")
    expected = set()
    for row in ledger["records"]:
        if row["status"] == "solver_unsat":
            k = key(row)
            expected.add(k)
            proof = cases[k]
            require(proof["verifier"].startswith("VERIFIED UNSAT ")
                    and proof["proof_sha256"] == row["lrat"]["sha256"]
                    and proof["regenerated_cnf_sha256"] == row["cnf"]["sha256"], "Mismatched proof receipt")
        else:
            require(row["status"] == "unknown", "Unexpected query outcome")
    require(expected == set(cases) and ledger["pending"] == 0, "Incomplete certificate inventory")
    return cases


def residual(parent, step):
    # The old head and every neighbour of it except the chosen first step
    # are unavailable. A parent neighbour already blocked stays blocked.
    allowed = (set(range(256)) - set(parent) - set(partner.NEIGHBOURS[0])) | {step}
    reached = {step}
    queue = [step]
    for v in queue:
        for u in partner.NEIGHBOURS[v]:
            if u in allowed and u not in reached:
                reached.add(u)
                queue.append(u)
    return frozenset(u ^ step for u in reached), len(allowed)


def features(points):
    shells = [0] * 9
    ones = [[0] * 9 for _ in AXES]
    pairs = [[0] * 8 for _ in AXES]
    for v in points:
        weight = v.bit_count()
        shells[weight] += 1
        indices = [i for i in AXES if v & (1 << i)]
        for i in indices:
            ones[i][weight] += 1
            for j in indices:
                pairs[i][j] += 1
    # Count both signs at each radius, so inclusion gives entrywise inequalities.
    profiles = [tuple(ones[i] + [n - r for n, r in zip(shells, ones[i])]) for i in AXES]
    return tuple(shells), profiles, pairs


def relabel(v, perm):
    return sum(1 << perm[i] for i in AXES if v & (1 << i))


def pointwise_check(src, dest, perm):
    require(sorted(perm) == list(AXES), "Axis map is not a permutation")
    image = {relabel(x, perm) for x in src}
    require(len(image) == len(src) and 0 in image and image <= dest, "Invalid residual inclusion map")
    return sha256(bytes(sorted(image))).hexdigest()


def embeddings(src, dest):
    points, (shells, axes, pairs) = src
    target, (other_shells, other_axes, other_pairs) = dest
    tested = 0
    accepted = 0
    witness = None
    if all(x <= y for x, y in zip(shells, other_shells)):
        candidates = [[j for j in AXES if all(x <= y for x, y in zip(axes[i], other_axes[j]))]
                      for i in AXES]
        perm = [-1] * 8
        order = sorted(AXES, key=lambda i: len(candidates[i]))

        def extend(depth, used):
            nonlocal tested, accepted, witness
            if depth == len(AXES):
                tested += 1
                if all(relabel(x, perm) in target for x in points):
                    accepted += 1
                    if witness is None:
                        witness = perm.copy()
                return
            i = order[depth]
            for j in candidates[i]:
                if used & (1 << j):
                    continue
                if any(pairs[i][k] > other_pairs[j][perm[k]] for k in order[:depth]):
                    continue
                perm[i] = j
                extend(depth + 1, used | (1 << j))
                perm[i] = -1

        extend(0, 0)
    result = dict(filtered_permutations=AXIS_MAPS - tested, tested_permutations=tested, valid_maps=accepted)
    if witness is not None:
        result.update(axes=witness, image_sha256=pointwise_check(points, target, witness))
    return result


def main():
    pins = {}
    roots = read_evidence("partners.json", pins)
    children = read_evidence("partner-children.json", pins)
    root_replay = read_evidence("partners-lrat.json", pins)
    child_replay = read_evidence("partner-children-lrat.json", pins)
    root_certs = checked_queries(roots, root_replay, pins["partners.json"])
    child_certs = checked_queries(children, child_replay, pins["partner-children.json"])
    child_keys = {(r["class_id"], r["endpoint"], tuple(r["prefix"])) for r in children["records"]}
    base = partner.parent_arms()
    descriptions, graphs = {}, {}
    tags = Counter()
    used_children = set()
    for row in roots["coverage"]:
        label, endpoint = row["class_id"], row["endpoint"]
        parent = partner.rooted_parent(base[label], endpoint)
        firsts = partner.next_vertices(parent, [0])
        require(parent == row["rooted_parent"] and firsts == row["next_vertices"] and len(firsts) == 7,
                "Rooted parent or first-step inventory changed")
        for s in firsts:
            case = f"c{label}-e{endpoint}-s{s}"
            require(case not in descriptions, "Repeated rooted first-step case")
            root_key, child_key = (label, endpoint, (0,)), (label, endpoint, (0, s))
            if root_key in root_certs:
                tag, proof = "whole_root_exclusion", root_certs[root_key]
            else:
                require(child_key in child_keys, "First-step query missing")
                used_children.add(child_key)
                proof = child_certs.get(child_key)
                tag = "first_step_exclusion" if proof else "unresolved"
            points, before = residual(parent, s)
            graphs[case] = (points, features(points))
            descriptions[case] = dict(class_id=label, endpoint=endpoint, first_step=s, evidence=tag,
                                      prior_proof_sha256=proof["proof_sha256"] if proof else None,
                                      allowed_before_reachability=before, reachable=len(points),
                                      normalized_vertices=sorted(points))
            tags[tag] += 1
    require(used_children == child_keys and tags == {"first_step_exclusion": 26, "whole_root_exclusion": 28,
                                                    "unresolved": 16}, "First-step evidence counts changed")

    # Roots are now all zero. Coordinate permutations are the entire rooted
    # ambient cube group. Equal finite cardinalities turn inclusion into equality.
    groups = []
    for key, src in graphs.items():
        for group in groups:
            rep = group["representative"]
            if len(src[0]) != len(graphs[rep][0]):
                continue
            maps = embeddings(src, graphs[rep])
            if maps["valid_maps"]:
                require(maps["valid_maps"] == group["stabilizer_order"], "Inconsistent isometry coset size")
                group["members"].append(dict(case=key, to_representative=maps["axes"],
                                             image_sha256=maps["image_sha256"]))
                break
        else:
            self_maps = embeddings(src, src)
            count = self_maps["valid_maps"]
            require(count and AXIS_MAPS % count == 0, "Invalid rooted stabilizer")
            groups.append(dict(representative=key, stabilizer_order=count, orbit_size=AXIS_MAPS // count,
                               members=[dict(case=key, to_representative=self_maps["axes"],
                                             image_sha256=self_maps["image_sha256"])]))

    old = [k for k, row in descriptions.items() if row["evidence"] != "unresolved"]
    pending = [k for k, row in descriptions.items() if row["evidence"] == "unresolved"]
    comparisons = []
    transferred = []
    for key in pending:
        targets = []
        for other in old:
            maps = embeddings(graphs[key], graphs[other])
            comparisons.append(dict(source=key, target=other, **maps))
            if maps["valid_maps"]:
                targets.append(other)
        if targets:
            transferred.append(dict(case=key, certified_targets=targets))
    output = dict(input_sha256=pins, source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  rooted_cases=descriptions, evidence_counts=tags, residual_isometry_classes=groups,
                  group_order=AXIS_MAPS, containment_pairs=comparisons, transferred=transferred,
                  remaining=[k for k in pending if k not in {r["case"] for r in transferred}],
                  map_convention="x -> permute(x XOR source_first_step) XOR target_first_step in rooted-parent labels")
    (HERE / "transfer.json").write_text(json.dumps(output, separators=(",", ":")) + "\n",
                                        encoding="utf-8", newline="\n")
    print("Compared", len(graphs), "rooted residuals in", len(groups), "isometry classes;",
          len(comparisons), "containment pairs;", len(transferred), "first-step exclusions transferred")


if __name__ == "__main__":
    main()
