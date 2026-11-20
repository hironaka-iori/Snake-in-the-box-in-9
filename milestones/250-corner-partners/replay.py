"""Replay one target ledger and determine its coverage at both ends of seven parents."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
PREV = HERE.parent / "249-long-parent-joins"
sys.path.insert(0, str(PREV))
import joins
from audit import check_cycle, file_hash, path_ok, require, rooted, verified_partner
from audit98 import open_prefixes

SHAPES = {"16:72", "17:71", "19:72", "99:85", "114:85", "901:72", "902:72"}


def read(path):
    return json.loads(path.read_bytes())


def provenance():
    paths = [HERE / "partners.py", PREV / "geometry.json", PREV / "audit.json",
             joins.INVENTORY, Path(joins.__file__), Path(joins.opposite.__file__),
             Path(joins.partner.__file__), joins.LAST / "endpoint94.py", joins.LAST / "certify.py",
             PREV / "direct98.py", PREV / "audit.py", joins.partner.PREV / "free_outer.py",
             joins.partner.SOURCE / "arc_sat.py", joins.CHECKER, joins.COMPILER, joins.partner.SOLVER]
    return {path.name: file_hash(path) for path in paths}


def rooted_cases():
    prior = read(PREV / "audit.json")
    source = joins.INVENTORY.relative_to(HERE.parents[1]).as_posix()
    require(prior["inputs"][source] == file_hash(joins.INVENTORY), "Old bound used a different inventory")
    caps = {(r["donor"], r["endpoint"]): r["upper"] for r in prior["cases"]}
    originals = {r["donor_index"]: r["path"] for r in read(joins.INVENTORY)["rows"]}
    rows = read(PREV / "geometry.json")["corner_closure"]["new_shapes"]
    require(len(rows) == 7 and {r["id"] for r in rows} == SHAPES, "Unexpected seven-shape inventory")
    cases = {}
    for r in rows:
        old, new, k = originals[r["parent"]], r["path"], r["position"]
        label = r["id"]
        require(label == f"{r['parent']}:{k}" and 0 < k < len(old)-1 and len(new) == len(old)
                and [i for i, (a, b) in enumerate(zip(old, new)) if a != b] == [k]
                and old[k] == r["removed"] and new[k] == r["inserted"]
                and new[k] == old[k-1] ^ old[k] ^ old[k+1]
                and [new[0], new[-1]] == r["endpoints"]
                and sha256(bytes(new)).hexdigest() == r["vertex_bytes_sha256"], ("Corner change", label))
        path_ok(old, 8)
        path_ok(new, 8)
        for end in (0, 1):
            original, changed = rooted(old, end), rooted(new, end)
            root = new[-1] if end else new[0]
            hit = old[k] ^ root
            require(set(original) - set(changed) == {hit} and set(changed) - set(original) == {new[k] ^ root}
                    and hit != 0, ("Freed site at joining endpoint", label, end))
            cases[label, end] = (changed, hit, caps[r["parent"], end])
    return cases


def reconstruct(parent, length, prefix, hit, cap):
    # The base formula is shared with the archived rooted encodings. Independently
    # derive the additional unit and cardinality clauses from the old parent's cap.
    if length == 95:
        cnf, chosen = joins.partner.encode(parent, prefix)
    elif length == 94:
        cnf, chosen = joins.encode94(parent, prefix)
    else:
        cnf, chosen = joins.opposite.encode(parent, length, prefix)
    require(set(chosen) == set(range(256)) - set(parent[1:]), "Incorrect full-parent domain")
    if length > cap:
        # Every prefix of cap+1 edges avoids all old-parent sites except the root
        # unless it includes hit. Its existence forces 1 <= position(hit) <= cap+1.
        cnf.clauses.append([chosen[hit]])
        if length > cap+1:
            # The forced site is internal, so at least two of its neighbours occur.
            ns = [chosen[w] for axis in range(8) if (w := hit ^ (1 << axis)) in chosen]
            if len(ns) < 2:
                cnf.clauses.append([])
            else:
                cnf.clauses.extend(list(group) for group in combinations(ns, len(ns)-1))
    return cnf, chosen


def replay_row(row, case, target, cnf_path, checker, proofs):
    parent, hit, cap = case
    length, prefix = target-len(parent), row["prefix"]
    require(row["length"] == length and row["old_cap"] == cap and row["hit"] == hit
            and 1 <= len(prefix) <= length+1 and prefix[0] == 0 and set(prefix) & set(parent) == {0},
            ("Rooted ledger entry", row["id"], row["end"]))
    path_ok(prefix, 8)
    cnf, chosen = reconstruct(parent, length, prefix, hit, cap)
    steps = row["steps"]
    require(steps and row["status"] in {"excluded", "open", "witness"}, "Incomplete ledger row")
    for i, step in enumerate(steps):
        digest = cnf.save(cnf_path)
        require(digest == step["cnf"] and cnf.count == step["variables"]
                and len(cnf.clauses) == step["clauses"], ("Regenerated CNF differs", digest))
        kind = step["outcome"]
        if i+1 < len(steps):
            require(kind == "cycles" and step["cycles"], "Missing intermediate cycle cut")
            cnf.clauses.extend(check_cycle(cycle, chosen) for cycle in step["cycles"])
            continue
        require(kind == row["status"], "Mismatched final outcome")
        if kind == "excluded":
            expected = "proofs/" + digest + ".lrat.gz"
            require(row["proof"] == expected, "Proof filename differs from the formula digest")
            if digest not in proofs:
                proof = HERE / expected
                compressed, raw = file_hash(proof), file_hash(proof, gzip.open)
                result = subprocess.run([str(checker), str(cnf_path), str(proof)], capture_output=True,
                                        timeout=120, check=True)
                receipt = result.stdout.decode("ascii").strip()
                require(receipt.startswith(f"VERIFIED UNSAT variables={cnf.count} input_clauses={len(cnf.clauses)} "),
                        ("Checker failed to verify formula", digest))
                proofs[digest] = dict(compressed=compressed, raw=raw, replay=receipt)
            require(all(row[k] == v for k, v in proofs[digest].items()), ("LRAT hash or replay receipt", digest))
        elif kind == "witness":
            verified_partner(parent, row, length)
            arm = row["partner"]
            require(arm[:len(prefix)] == prefix and row["joined_edges"] == target, "Witness ordered prefix or length")
            if length > cap:
                require(hit in arm[1:cap+2], "Witness evades the required site or reaches it too late")
                if length > cap+1:
                    require(sum((v ^ hit).bit_count() == 1 for v in arm) == 2,
                            "Forced internal site is not internal in the witness")


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--target", type=int, choices=range(180, 193), default=192)
    target = cli.parse_args().target
    ledger = HERE / f"target-{target}.json"
    raw = ledger.read_bytes()
    data = json.loads(raw)
    require(data["target"] == target and data["pins"] == provenance(), "Target or dependency hashes differ")
    cases = rooted_cases()
    groups, proofs = defaultdict(list), {}
    with TemporaryDirectory(prefix="snake250-replay-") as temp:
        checker = Path(temp) / "VerifyLrat.exe"
        subprocess.run([str(joins.COMPILER), "/nologo", "/optimize+", "/out:" + str(checker), str(joins.CHECKER)],
                       check=True, capture_output=True, timeout=60)
        for row in data["records"]:
            key = row["id"], row["end"]
            require(key in cases, ("Unexpected target case", key))
            replay_row(row, cases[key], target, Path(temp) / "root.cnf", checker, proofs)
            groups[key].append(row)
        checker_hash = file_hash(checker)
    result = []
    for key, (parent, hit, cap) in sorted(cases.items()):
        rows = groups[key]
        length = target-len(parent)
        prefixes = [tuple(r["prefix"]) for r in rows]
        require(len(prefixes) == len(set(prefixes)), ("Duplicate prefix", key))
        pending = open_prefixes(parent, length, rows)
        witnesses = [r["partner"] for r in rows if r["status"] == "witness"]
        for arm in witnesses:
            require(pending and all(arm[:len(r["prefix"])] != r["prefix"] for r in rows if r["status"] == "excluded"),
                    ("Witness contradicts an exclusion", key))
        status = "witness" if witnesses else ("open" if pending else "excluded")
        result.append(dict(id=key[0], end=key[1], partner_edges=length, freed_site=hit, old_cap=cap,
                           required_hit_by=cap+1 if length > cap else None, internal=length > cap+1,
                           status=status, rows=len(rows), witnesses=len(witnesses), open_prefixes=pending))
    counts = Counter(r["status"] for r in result)
    out = dict(target=target, ledger_sha256=sha256(raw).hexdigest(), audit_source_sha256=file_hash(Path(__file__)),
               coverage_source_sha256=file_hash(PREV / "audit98.py"), checker_executable_sha256=checker_hash,
               dependency_hashes=data["pins"], records=len(data["records"]), cycles_checked=sum(
                   len(step.get("cycles", [])) for r in data["records"] for step in r["steps"]),
               distinct_proofs_replayed=len(proofs), proofs=proofs, endpoint_counts=dict(counts),
               all_endpoints_decided=counts["open"] == 0, excluded_at_all_endpoints=counts["excluded"] == len(cases),
               endpoints=result, scope="Seven archived corner-changed parents, both endpoints, one crossing, "
               "at the stated joined length. Old-parent caps come from the pinned Round 249 audit.")
    joins.save_json(HERE / f"replay-{target}.json", out)
    print(f"Target {target}, {len(cases)} endpoints, {dict(counts)}, {len(proofs)} distinct LRAT replays.", flush=True)


if __name__ == "__main__":
    main()
