"""Audit coverage, certificate bindings and explicit maximizers without invoking a solver."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import re

from survey import HERE, PREVIOUS, partner, save_json
from endpoint94 import encode94


OLDER = partner.PREV
BANK = HERE.parents[1] / "work" / "bank9.json"
COMPILER = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")
INPUTS = {}


def require(ok, detail):
    if not ok:
        raise ValueError(detail)


def read(path):
    raw = path.read_bytes()
    INPUTS[str(path.relative_to(HERE.parents[1])).replace("\\", "/")] = sha256(raw).hexdigest()
    return json.loads(raw)


def pins(data):
    for name, expected in data.get("pins", {}).items():
        possible = [p for p in (HERE/name, PREVIOUS/name, OLDER/name, partner.SOURCE/name,
                                BANK, COMPILER, partner.SOLVER) if p.name == name and p.is_file()]
        require(any(partner.digest(p) == expected for p in possible), ("Source pin", name))


def unique(rows, key):
    table = {key(r): r for r in rows}
    require(len(table) == len(rows), "Duplicate case")
    return table


def archive(directory, filename, compressed, raw, size=None):
    path = directory / filename
    require(partner.digest(path) == compressed, ("Archive digest", filename))
    digest = sha256()
    length = 0
    with gzip.open(path, "rb") as f:
        for block in iter(lambda: f.read(131072), b""):
            length += len(block)
            digest.update(block)
    require(length and (size is None or length == size) and digest.hexdigest() == raw,
            ("Uncompressed artifact", filename))


def check_proof(statement, cnf):
    match = re.fullmatch(r"VERIFIED UNSAT variables=(\d+) input_clauses=(\d+) additions=(\d+) "
                         r"deleted_clauses=(\d+) hints=(\d+) empty_id=(\d+)", statement)
    require(match and int(match[1]) == cnf.count and int(match[2]) == len(cnf.clauses)
            and int(match[3]) > 0 and int(match[6]) > len(cnf.clauses), "LRAT receipt does not match DIMACS")


def path_check(path, dimension):
    require(0 < len(path) == len(set(path)) and all(0 <= v < 2**dimension for v in path),
            "Invalid vertex label or repeated path vertex")
    for (i, u), (j, v) in combinations(enumerate(path), 2):
        require(((u ^ v).bit_count() == 1) == (j == i + 1), ("Bad adjacency", dimension, i, j))


def root_signature(path):
    # The gaps since the last occurrence of a flipped axis determine its
    # equality pattern. A zero introduces an axis never seen previously.
    last = {}
    word = []
    for i, (u, v) in enumerate(zip(path, path[1:])):
        bit = u ^ v
        word.append(i - last[bit] if bit in last else 0)
        last[bit] = i
    return tuple(word)


def shape(path):
    return min(root_signature(path), root_signature(path[::-1]))


def join(parent, p, length):
    require(parent[0] == p[0] == 0 and len(p) == length + 1 and set(parent) & set(p) == {0},
            "Invalid rooted join")
    path_check(parent, 8)
    path_check(p, 8)
    joined = parent[::-1] + [v + 256 for v in p]
    path_check(joined, 9)
    return joined


def cut(chosen, vertices):
    points = set(vertices)
    require(len(points) == len(vertices) >= 4 and points <= chosen.keys(), "Invalid cycle vertices")
    reached = {vertices[0]}
    todo = list(reached)
    for v in todo:
        adjacent = [u for u in points if (u ^ v).bit_count() == 1]
        require(len(adjacent) == 2, "Clause does not block a cycle")
        for u in adjacent:
            if u not in reached:
                reached.add(u)
                todo.append(u)
    require(reached == points, "Disconnected cycle cut")
    return [-chosen[v] for v in sorted(points)]


def reconstruct95(parent, prefix, initial, attempts, filename, new):
    cnf, chosen = partner.encode(parent, prefix)
    for cycle in initial:
        cnf.clauses.append(cut(chosen, cycle))
    for step in attempts:
        require(cnf.save(filename) == step["cnf" if new else "cnf_sha256"], "Intermediate 95-edge CNF changed")
        for cycle in step.get("cycles", []):
            cnf.clauses.append(cut(chosen, cycle))
    return cnf


def old_proofs(stem, parents, filename):
    source = PREVIOUS / (stem + ".json")
    ledger = read(source)
    replay = read(PREVIOUS / (stem + "-lrat.json"))
    pins(ledger)
    require(not ledger["pending"] and replay["source_sha256"] == partner.digest(source)
            and replay["checker_source_sha256"] == partner.digest(OLDER / "VerifyLrat.cs")
            and replay["compiler_sha256"] == partner.digest(COMPILER), "Old receipt provenance")
    key = lambda r: (r["class_id"], r["endpoint"], tuple(r["prefix"]))
    rows = unique(ledger["records"], key)
    proofs = unique(replay["cases"], key)
    require(len(proofs) == replay["verified"] == replay["solver_exclusions"]
            and set(proofs) == {k for k, r in rows.items() if r["status"] == "solver_unsat"}, "Old proof coverage")
    for k, proof in proofs.items():
        row = rows[k]
        cnf = reconstruct95(parents[k[:2]], k[2], row["initial_cycles"], row["attempts"], filename, False)
        require(row["attempts"][-1]["result"] == "UNSAT"
                and cnf.save(filename) == row["cnf"]["sha256"] == proof["regenerated_cnf_sha256"]
                and row["lrat"]["sha256"] == proof["proof_sha256"], "Old proof inputs")
        check_proof(proof["verifier"], cnf)
        for part in ("cnf", "lrat"):
            a = row[part]
            archive(PREVIOUS, a["file"], a["gzip_sha256"], a["sha256"], a["bytes"])
    require(all(r["status"] in ("solver_unsat", "unknown") for r in rows.values()), "Unexpected old outcome")
    return rows, proofs


def coverage(parents, filename):
    roots, certified_roots = old_proofs("partners", parents, filename)
    kids, certified_kids = old_proofs("partner-children", parents, filename)
    require(set(roots) == {(i, e, (0,)) for i, e in parents}, "Wrong endpoint inventory")
    starts = {(i, e, 1 << j) for (i, e), p in parents.items() for j in range(8) if (1 << j) not in p}
    direct = {k for k in starts if (*k[:2], (0,)) in certified_roots}
    require(set(kids) == {(i, e, (0, s)) for i, e, s in starts - direct}, "Wrong first-step partition")
    closed = {(i, e, p[1]) for i, e, p in certified_kids}
    require(not direct & closed and (len(starts), len(direct), len(closed)) == (70, 28, 26),
            "Unexpected inherited cover")
    survey, certs = read(HERE / "survey.json"), read(HERE / "certificates.json")
    pins(survey)
    pins(certs)
    key = lambda r: tuple(r["case"])
    queried, verified = unique(survey["records"], key), unique(certs["records"], key)
    require(set(queried) == set(verified) == starts - direct - closed and len(verified) == 16,
            "New exclusions do not cover exactly the remaining first steps")
    result = []
    for k, cert in verified.items():
        row = queried[k]
        cnf = reconstruct95(parents[k[:2]], [0, k[2]], [], row["attempts"], filename, True)
        require(row["status"] == "native_unsat"
                and cnf.save(filename) == row["final_cnf"] == cert["cnf_sha256"], "New 95-edge formula")
        check_proof(cert["verified"], cnf)
        archive(HERE, cert["proof"], cert["gzip_sha256"], cert["raw_sha256"], cert["raw_bytes"])
        result.append(dict(case=k, cnf_sha256=cert["cnf_sha256"], raw_sha256=cert["raw_sha256"]))
    endpoints = [dict(case=k, starts=sorted(s for i, e, s in starts if (i, e) == k),
                      prior_root=(*k, (0,)) in certified_roots,
                      prior_first=sorted(s for i, e, s in closed if (i, e) == k),
                      new_first=sorted(s for i, e, s in verified if (i, e) == k)) for k in parents]
    return dict(endpoints=endpoints, prior_root_proofs=len(certified_roots), prior_first_proofs=len(certified_kids),
                new_first_proofs=result, covered_first_steps=len(starts))


def endpoint_cover(parents, published, bank_words, filename):
    data = read(HERE / "endpoint94.json")
    pins(data)
    rows = unique(data["records"], lambda r: tuple(r["case"]))
    require(rows.keys() == parents.keys(), "Incomplete 94-edge endpoint coverage")
    witness_sets = {}
    seen_seeds = set()
    for k, row in rows.items():
        parent = parents[k]
        require(row["rooted_parent"] == parent, "Wrong 94-edge parent")
        seen = {}
        for w in row["known_bank_witnesses"]:
            seed = w["seed"]
            original = published[seed]
            images = w["axis_images"]
            require(sorted(images) == [1 << j for j in range(8)], "Invalid axis permutation")
            def transport(p):
                return [w["translation"] ^ sum(images[j] for j in range(8) if v & (1 << j)) for v in p]
            p = w["partner"]
            full = join(parent, p, 94)
            require(transport(original["long"]) == parent and transport(original["short"]) == p
                    and seed == bank_words[shape(full)] and full == w["joined"]
                    and w["crossing_axis"] == original["axis"] and w["edges"] == 191,
                    "Archived bank transport or joined path changed")
            require(seed not in seen_seeds and frozenset(p) not in seen, "Duplicate published control")
            seen[frozenset(p)] = seed
            seen_seeds.add(seed)
        root_excluded = False
        for trial in row["queries"]:
            if trial["status"] == "witness":
                require(join(parent, trial["partner"], 94) == trial["joined"], "Invalid queried witness")
                continue
            if trial["status"] != "verified_exclusion":
                require(trial["status"] == "unknown", "Unexpected endpoint query")
                continue
            cnf, chosen = encode94(parent, trial["prefix"])
            for cycle in trial["cycles"]:
                cnf.clauses.append(cut(chosen, cycle))
            require(cnf.save(filename) == trial["cnf_sha256"] == trial["attempts"][-1]["cnf_sha256"]
                    and trial["attempts"][-1]["result"] == "verified_unsat", "Endpoint94 formula changed")
            archive(HERE, trial["proof"], trial["gzip_proof_sha256"], trial["raw_proof_sha256"])
            check_proof(trial["checker"], cnf)
            root_excluded |= trial["prefix"] == [0]
        if "donor_witness" in row:
            w = row["donor_witness"]
            require(join(parent, w["partner"], 94) == w["joined"], "Invalid donor witness")
        require((k[1] == 0 and len(seen) == 5 and row["status"] == "bank_witness" and not root_excluded)
                or (k[1] == 1 and root_excluded and not seen and row["status"] == "verified_exclusion"),
                "Unproven 94-edge endpoint classification")
        witness_sets[k] = seen
    require(seen_seeds == set(published), "Missing a published control")
    return witness_sets


def audit_attainers(parents, positives, bank_words, filename):
    source = HERE / "attainers.json"
    if not source.exists():
        return dict(available=False)
    census = read(source)
    pins(census)
    rows = unique(census["records"], lambda r: r["class_id"])
    require(set(rows) == {i for i, e in parents}, "Missing an attainer census")
    by_class = []
    rooted, unoriented, joins = set(), set(), set()
    labels = Counter()
    for i, row in rows.items():
        parent = parents[i, 0]
        known = positives[i, 0]
        cnf, chosen = encode94(parent)
        seen, class_partners, class_joins, bank_ids = set(), set(), set(), []
        for ent in row["paths"]:
            p = ent["path"]
            sequence = join(parent, p, 94)
            key, word = frozenset(p), shape(sequence)
            require(key not in seen and sequence == ent.get("joined", sequence), "Repeated path or incorrect join")
            require(ent["in_bank"] == (word in bank_words), "Bank membership disagreement")
            if key in known or "seed" in ent:
                require(known[key] == ent["seed"] == bank_words[word], "Seed membership differs")
            seen.add(key)
            cnf.clauses.append([-chosen[v] for v in sorted(key)])
            class_partners.add(root_signature(p))
            class_joins.add(word)
            if word in bank_words:
                bank_ids.append(bank_words[word])
            labels["inside" if word in bank_words else "outside"] += 1
            unoriented.add(shape(p))
        require(set(known) <= seen, "Published partner missing from enumeration")
        for cycle in row["cycles"]:
            cnf.clauses.append(cut(chosen, cycle))
        summary = dict(class_id=i, status=row["status"], labelled=len(seen), rooted_partner_shapes=len(class_partners),
                       whole_join_shapes=len(class_joins), bank_ids=sorted(bank_ids), blocked_cycles=len(row["cycles"]))
        if row["status"] == "exhausted":
            require(cnf.save(filename) == row["cnf_sha256"], "Attainer exhaustion CNF changed")
            check_proof(row["verified"], cnf)
            archive(HERE, row["proof"], row["gzip_sha256"], row["raw_sha256"])
            summary.update(cnf_sha256=row["cnf_sha256"], raw_sha256=row["raw_sha256"])
        else:
            require(row["status"] in ("time_limit", "path_limit", "searching"), "Unknown census status")
        by_class.append(summary)
        rooted.update(class_partners)
        joins.update(class_joins)
    return dict(available=True, complete=all(r["status"] == "exhausted" for r in by_class),
                labelled=sum(labels.values()), labelled_joins_in_bank=labels["inside"], labelled_joins_outside_bank=labels["outside"],
                rooted_partner_shapes=len(rooted), partner_shapes_up_to_reversal=len(unoriented),
                whole_join_shapes=len(joins), whole_join_shapes_in_bank=len(joins & bank_words.keys()),
                whole_join_shapes_outside_bank=len(joins - bank_words.keys()), cases=by_class)


def positive_controls(published, inventory, filename):
    control_file = HERE / "controls.json"
    if not control_file.exists():
        return dict(available=False)
    data = read(control_file)
    pins({"pins": data["inputs"]})
    rows = unique(data["checks"], lambda r: r["bank_seed"])
    require(rows.keys() == published.keys(), "Incomplete positive controls")
    by_seed = {seed: (a, b) for a, line in zip(inventory["long_class_ids"], inventory["seed_ids_by_long_row_short_column"])
               for b, seed in zip(inventory["short_class_ids"], line)}
    for seed, item in rows.items():
        source = published[seed]
        obstacle, target = source["short"], source["long"][:-1]
        alternate = join(obstacle, target, 95)
        require(len(alternate) == 191 and item["pinned_prefix"] == target[:2]
                and by_seed[seed] == (item["long_class"], item["short_class"]), "Wrong positive control")
        cnf, chosen = partner.encode(obstacle, target[:2])
        fixed = set(target)
        cnf.clauses.extend([lit if v in fixed else -lit] for v, lit in chosen.items())
        require(cnf.save(filename) == item["positive_cnf_sha256"] and item["pinned_sat"] is True,
                "Changed positive-control CNF")
    return dict(available=True, checked_swapped_paths=len(rows), regenerated_pinned_cnfs=len(rows))


def main():
    bank = read(BANK)
    bank_words = {}
    for i, row in enumerate(bank):
        path = row["vertex_sequence"]
        require(len(path) == 192, "Bank path length")
        path_check(path, 9)
        bank_words[shape(path)] = i
    require(len(bank_words) == len(bank) == 131, "Published class inventory")
    comparison = read(OLDER / "comparison.json")
    inventory = read(OLDER / "arm-structure.json")
    published = unique(comparison["one_crossing_pairs"], lambda r: r["seed"])
    require(len(published) == 25 and len(set(inventory["long_class_ids"])) == 5, "Published parent inventory")
    parents = {}
    for i in inventory["long_class_ids"]:
        long = published[i]["long"]
        require(len(long) == 97, "Parent length")
        for e, ordered in enumerate((long, long[::-1])):
            parents[i, e] = [v ^ ordered[0] for v in ordered]
    for seed, row in published.items():
        require(bank_words[shape(join(row["long"], row["short"], 94))] == seed, "Published arm pair provenance")
    with TemporaryDirectory(prefix="snake248-aggregate-") as directory:
        filename = Path(directory) / "audit.cnf"
        cover = coverage(parents, filename)
        positives = endpoint_cover(parents, published, bank_words, filename)
        census = audit_attainers(parents, positives, bank_words, filename)
        controls = positive_controls(published, inventory, filename)
    other_witnesses = []
    if (HERE/"opposite.json").exists():
        opposite = read(HERE/"opposite.json")
        pins(opposite)
        for r in opposite["records"]:
            i = r["class_id"]
            parent = parents[i, 1]
            witnesses = [r["lower_witness"]] + [t for q in r["length_queries"].values() for t in q if t["status"] == "witness"]
            for w in witnesses:
                require(join(parent, w["partner"], w["partner_edges"]) == w["joined"]
                        and w["joined_edges"] == len(w["joined"])-1, "Invalid opposite-end witness")
            other_witnesses.append(dict(class_id=i, verified=len(witnesses), lower_witness_edges=r["lower_witness"]["partner_edges"]))
    save_json(HERE/"aggregate.json", dict(source_sha256=partner.digest(Path(__file__)), inputs=INPUTS,
              scope="Checks archived proof bytes, matching prior LRAT acceptance receipts and regenerated DIMACS. No solver or proof-checker invocation.",
              canonical_form="Axis recurrence gaps; oriented order for rooted partners, minimum of both orders for unrooted partners and complete joins.",
              coverage95=cover, endpoint94=[dict(case=k, verified_bank_witnesses=len(v), upper_excluded=k[1]==1) for k,v in positives.items()],
              attainers=census, positive_controls=controls, additional_opposite_witnesses=other_witnesses))
    print("95-edge first steps covered", cover["covered_first_steps"], "published joins", len(published),
          "attainers", census.get("labelled"), "whole join classes", census.get("whole_join_shapes"))


if __name__ == "__main__":
    main()
