"""Search or independently replay unrestricted opposite-face partners for a census."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from functools import lru_cache
import gzip
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "250-corner-partners"
PREV = HERE.parent / "249-long-parent-joins"
sys.path.insert(0, str(PREV))
import joins
from audit import check_cycle, file_hash, path_ok, require, rooted, verified_partner
from direct98 import witness
from geometry import shape


def read(path):
    return json.loads(path.read_bytes())


def pins(census):
    files = [Path(__file__), census, joins.INVENTORY, PREV / "geometry.json", PREV / "audit.json",
             PREV / "audit98.json", LAST / "cores-84.json", LAST / "replay-191.json",
             LAST / "extended-audit-191.json", PREV / "joins.py", PREV / "geometry.py", PREV / "audit.py",
             PREV / "direct98.py", joins.LAST / "opposite.py", joins.LAST / "endpoint94.py",
             joins.LAST / "certify.py", Path(joins.partner.__file__), joins.partner.PREV / "free_outer.py",
             joins.partner.SOURCE / "arc_sat.py", joins.CHECKER, joins.COMPILER, joins.partner.SOLVER]
    return {p.name: file_hash(p) for p in files}


def known_parents():
    originals = {r["donor_index"]: r["path"] for r in read(joins.INVENTORY)["rows"]}
    parents = {str(k): p for k, p in originals.items()}
    caps = {(str(r["donor"]), r["endpoint"]): r["upper"] for r in read(PREV / "audit.json")["cases"]}
    full = originals[20]
    for case in read(PREV / "audit98.json")["cases"]:
        end = [full[0], full[-1]].index(case["root"])
        caps["20", end] = min(caps["20", end], case["partner"]["upper"])
    for shapes, evidence in [
        (read(PREV / "geometry.json")["corner_closure"]["new_shapes"], read(LAST / "replay-191.json")["endpoints"]),
        (read(LAST / "cores-84.json")["new_shapes"], read(LAST / "extended-audit-191.json")["endpoints"]),
    ]:
        parents.update({r["id"]: r["path"] for r in shapes})
        for r in evidence:
            label, end = r["id"], r["end"]
            length = 191 - len(parents[label])
            require(r["status"] == "excluded" and r.get("partner_edges", r.get("length")) == length,
                    ("Expected archived rooted 191 exclusion", label, end))
            caps[label, end] = length-1
    require(len(parents) == 25 and len(caps) == 50, "Unexpected archived parent inventory")
    for p in parents.values():
        path_ok(p, 8)
    return {(k, e): (rooted(parents[k], e), cap) for (k, e), cap in caps.items()}, {shape(p) for p in parents.values()}


def census_cases(census, archived):
    cases = {}
    for row in read(census)["new_shapes"]:
        label, path = row["id"], row["path"]
        code = shape(path)
        path_ok(path, 8)
        require(sha256(code).hexdigest() == label and row["edges"] == len(path)-1 and 96 <= row["edges"] <= 98
                and code not in archived and (label, 0) not in cases, ("Incorrect or repeated new shape", label))
        for end in (0, 1):
            cases[label, end] = rooted(path, end)
    return cases


def windows(path, step):
    axes = [(a ^ b).bit_length()-1 for a, b in zip(path, path[1:])]
    for i in range(0, len(axes)-15, step):
        segment = axes[i:i+16]
        order = list(dict.fromkeys(segment))
        key = bytes(order.index(axis) for axis in segment)
        yield key, order + sorted(set(range(8))-set(order))


def placement_index(old):
    index = defaultdict(set)
    for key, (path, _) in old.items():
        for signature, order in windows(path, 1):
            index[signature].add((key, tuple(order)))
    return index


@lru_cache(maxsize=256)
def images(axes):
    require(sorted(axes) == list(range(8)), "Invalid rooted coordinate map")
    table = [0]
    for axis in axes:
        table += [x | (1 << axis) for x in table]
    return table


def transfers(parent, old, index):
    # Window matching only proposes axis permutations. Soundness comes from
    # reconstructing the entire old set at the common root before adding a cut.
    candidates = {(key, tuple(range(8))) for key in old}
    for signature, order in windows(parent, 5):
        for key, before in index.get(signature, ()):
            axes = tuple(order[before.index(k)] for k in range(8))
            candidates.add((key, axes))
    target = set(parent)
    retained = {}
    for key, axes in sorted(candidates):
        oldpath, cap = old[key]
        table = images(axes)
        freed = tuple(sorted({table[v] for v in oldpath}-target))
        if len(freed) <= 8 and (freed not in retained or cap < retained[freed]["cap"]):
            retained[freed] = dict(source=list(key), axes=list(axes), cap=cap, sites=list(freed))
    return sorted(retained.values(), key=lambda r: (len(r["sites"]), r["cap"], r["sites"]))


def active_cuts(candidates, length):
    result = []
    for rule in candidates:
        if rule["cap"] >= length:
            continue
        internal = length > rule["cap"]+1
        sites = set(rule["sites"])
        if any(set(r["sites"]) <= sites and (not internal or length > r["cap"]+1) for r in result):
            continue
        result.append(rule)
    return result


def validate_rules(parent, length, rules, old):
    for rule in rules:
        key = tuple(rule["source"])
        oldpath, cap = old[key]
        table = images(tuple(rule["axes"]))
        require(rule["sites"] == sorted({table[v] for v in oldpath} - set(parent))
                and rule["cap"] == cap < length, "Unjustified inherited cut")


def model(parent, length, rules):
    cnf, chosen = joins.encode(parent, length, [0], [])
    require(set(chosen) == set(range(256))-set(parent[1:]), "Incorrect rooted complement")
    for rule in rules:
        sites = rule["sites"]
        cnf.clauses.append([chosen[v] for v in sites])
        if length > rule["cap"]+1 and len(sites) <= 3:
            for v in sites:
                # If no other freed site is selected, this one must be internal.
                other = [chosen[w] for w in sites if w != v]
                neighbours = [chosen[w] for w in joins.partner.NEIGHBOURS[v] if w in chosen]
                joins.partner.bounds(cnf, neighbours, 2, len(neighbours), other)
    return cnf, chosen


def check_proof(cnf_path, proof, exe):
    response = subprocess.run([str(exe), str(cnf_path), str(proof)], capture_output=True, check=True, timeout=100)
    receipt = response.stdout.decode("ascii").strip()
    require(receipt.startswith("VERIFIED UNSAT "), "LRAT verifier did not certify a contradiction")
    return receipt


def solve(parent, length, rules, old, folder, exe, seconds, previous):
    validate_rules(parent, length, rules, old)
    if any(not r["sites"] for r in rules):
        return dict(status="inherited", rules=[next(r for r in rules if not r["sites"])])
    cnf, chosen = model(parent, length, rules)
    cnf_path, raw = folder / "partner.cnf", folder / "proof.lrat"
    cycles = list(previous.get("cycles", [])) if previous else []
    if previous:
        require(previous["rules"] == rules, "Saved cycle refinements use different premises")
    cnf.clauses.extend(check_cycle(c, chosen) for c in cycles)
    deadline = monotonic()+seconds
    while True:
        digest = cnf.save(cnf_path)
        raw.unlink(missing_ok=True)
        record = dict(rules=rules, cycles=cycles, cnf=digest, variables=cnf.count, clauses=len(cnf.clauses))
        try:
            answer = subprocess.run([str(joins.partner.SOLVER), "-q", "--seed=1", "--lrat", "--no-binary",
                                     str(cnf_path), str(raw)], capture_output=True, timeout=max(.01, deadline-monotonic()))
        except subprocess.TimeoutExpired:
            return dict(status="open", **record)
        if answer.returncode == 20 and b"s UNSATISFIABLE" in answer.stdout:
            proof = HERE / "proofs" / (digest + ".lrat.gz")
            proof.parent.mkdir(exist_ok=True)
            raw_hash = joins.archive(raw, proof)
            receipt = check_proof(cnf_path, proof, exe)
            return dict(status="excluded", **record, proof=proof.relative_to(HERE).as_posix(), raw=raw_hash,
                        compressed=file_hash(proof), replay=receipt)
        require(answer.returncode == 10 and b"s SATISFIABLE" in answer.stdout, "Unexpected solver outcome")
        truth = {int(t) for line in answer.stdout.splitlines() if line.startswith(b"v ")
                 for t in line.split()[1:] if int(t) > 0}
        selected = {v for v, lit in chosen.items() if lit in truth}
        require(selected & set(parent) == {0}, "Model intersects the archived parent")
        found, extra = joins.opposite.extract(parent[:97], length, [0], selected)
        if found:
            return dict(status="witness", **record, **witness(parent, found["partner"]))
        require(extra, "Disconnected model without a cycle")
        cnf.clauses.extend(check_cycle(c, chosen) for c in extra)
        cycles.extend(extra)


def replay(parent, length, row, old, folder, exe):
    rules = row["rules"]
    validate_rules(parent, length, rules, old)
    if row["status"] == "inherited":
        require(any(not r["sites"] for r in rules), "Old domain does not contain the new domain")
        return
    cnf, chosen = model(parent, length, rules)
    cnf.clauses.extend(check_cycle(c, chosen) for c in row["cycles"])
    cnf_path = folder / "reconstructed.cnf"
    digest = cnf.save(cnf_path)
    require((digest, cnf.count, len(cnf.clauses)) == (row["cnf"], row["variables"], row["clauses"]),
            "Reconstructed formula differs")
    if row["status"] == "excluded":
        name = "proofs/" + digest + ".lrat.gz"
        require(row["proof"] == name, "Proof filename does not bind to this formula")
        proof = HERE / name
        require(file_hash(proof) == row["compressed"] and file_hash(proof, gzip.open) == row["raw"]
                and check_proof(cnf_path, proof, exe) == row["replay"], "Proof digest or replay mismatch")
    elif row["status"] == "witness":
        verified_partner(parent, row, length)
        arm = row["partner"]
        require(all(set(arm[1:r["cap"]+2]) & set(r["sites"]) for r in rules), "Witness evades an inherited cut")
    else:
        require(row["status"] == "open", "Unknown recorded outcome")


def endpoint_status(key, target, rows):
    if target == 192:
        smaller = rows.get((*key, 191), {})
        if smaller.get("status") in {"excluded", "inherited"}:
            require(rows.get((*key, 192), {}).get("status") != "witness", "Long witness contradicts shorter exclusion")
            return "excluded_by_191"
    return rows.get((*key, target), {}).get("status", "unattempted")


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--core", default="80", help="core size or census JSON path")
    cli.add_argument("--target", type=int, choices=(191, 192), default=192)
    cli.add_argument("--id", help="full or unique initial characters of the canonical SHA")
    cli.add_argument("--end", type=int, choices=(0, 1))
    cli.add_argument("--limit", type=int, default=100000, help="maximum number of endpoints per invocation")
    cli.add_argument("--seconds", type=float, default=8, help="solver seconds per endpoint and target")
    cli.add_argument("--total", type=float, default=180, help="stop beginning new searches after this many seconds")
    cli.add_argument("--retry-open", action="store_true", help="resume and retry timed-out queries")
    cli.add_argument("--replay", action="store_true", help="reconstruct and replay all selected recorded targets")
    args = cli.parse_args()
    require(args.limit > 0 and args.seconds > 0 and args.total > 0, "Limits must be positive")
    core = f"census-{args.core}.json" if args.core.isdecimal() else args.core
    census = (HERE / core).resolve()
    ledger = HERE / f"partners-{census.stem}.json"
    dependencies = pins(census)
    old, archived = known_parents()
    cases = census_cases(census, archived)
    selected = list(cases)
    if args.id:
        labels = {label for label, _ in selected if label.startswith(args.id)}
        require(len(labels) == 1, "Shape ID is missing or ambiguous")
        selected = [k for k in selected if k[0] in labels]
    if args.end is not None:
        selected = [k for k in selected if k[1] == args.end]
    data = read(ledger) if ledger.exists() else dict(pins=dependencies, records=[])
    require(data["pins"] == dependencies, "Dependency or census digest changed")
    records = {(r["id"], r["end"], r["target"]): r for r in data["records"]}
    require(len(records) == len(data["records"]) and all((i, e) in cases and t in (191, 192) for i, e, t in records),
            "Duplicate entry or entry not in census")
    targets = [191] if args.target == 191 else [191, 192]
    if not args.replay:
        selected.sort(key=lambda k: sum((*k, t) in records for t in targets))
    index = {} if args.replay else placement_index(old)
    report = []
    deadline = monotonic()+args.total
    with TemporaryDirectory(prefix="snake251-partners-") as tmp:
        folder = Path(tmp)
        exe = folder / "VerifyLrat.exe"
        subprocess.run([str(joins.COMPILER), "/nologo", "/optimize+", "/out:"+str(exe), str(joins.CHECKER)],
                       capture_output=True, check=True, timeout=45)
        for key in selected:
            if len(report) >= args.limit or (not args.replay and monotonic() >= deadline):
                break
            parent = cases[key]
            rules = None
            handled = False
            for t in targets:
                rkey = (*key, t)
                previous = records.get(rkey)
                length = t-len(parent)
                if previous:
                    require(previous["length"] == length, "Stored target length differs")
                if args.replay:
                    if previous:
                        replay(parent, length, previous, old, folder, exe)
                    continue
                if t == 192 and endpoint_status(key, t, records) == "excluded_by_191":
                    break
                if previous and (previous["status"] != "open" or not args.retry_open):
                    continue
                if monotonic() >= deadline:
                    break
                if rules is None:
                    rules = transfers(parent, old, index)
                outcome = solve(parent, length, active_cuts(rules, length), old, folder, exe,
                                min(args.seconds, max(.01, deadline-monotonic())), previous)
                records[rkey] = dict(id=key[0], end=key[1], target=t, length=length, **outcome)
                data["records"] = list(records.values())
                joins.save_json(ledger, data)
                print(t, *key, outcome["status"], flush=True)
                handled = True
            if handled or args.replay:
                report.append(dict(id=key[0], end=key[1], status=endpoint_status(key, args.target, records)))
    if args.replay:
        tag = f"-{args.id}" if args.id else ""
        tag += f"-end{args.end}" if args.end is not None else ""
        tag += f"-first{args.limit}" if len(report) < len(selected) else ""
        counts = Counter(r["status"] for r in report)
        all_covered = len(report) == len(cases)
        receipt = dict(target=args.target, census=census.name, census_sha256=file_hash(census),
                       ledger_sha256=file_hash(ledger) if ledger.exists() else None, pins=dependencies,
                       all_census_endpoints_reviewed=all_covered, endpoints_in_census=len(cases),
                       all_excluded=all_covered and all(s in {"excluded", "inherited", "excluded_by_191"} for s in counts),
                       counts=counts, endpoints=report)
        joins.save_json(HERE / f"replay-{census.stem}-{args.target}{tag}.json", receipt)
        print("Endpoint outcomes:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
