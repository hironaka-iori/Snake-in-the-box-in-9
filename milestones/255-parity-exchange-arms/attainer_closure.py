"""Enumerate repeated single exchanges of the smaller parity class of a 96-edge arm."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic

HERE = Path(__file__).resolve().parent
R248 = HERE.parent / "248-rooted-arm-capacity"
R252 = HERE.parent / "252-shorter-reference-segments"
R253 = HERE.parent / "253-repeated-segment-growth"
R254 = HERE.parent / "254-distant-arm-partners"
sys.path.insert(0, str(R252))
from replay_core import check_path, digest, word
from replay_exchange import CSC, SEED


def shape(path):
    return sha256(word(path)).hexdigest()


def oriented_word(path):
    axes = {}
    return bytes(axes.setdefault(a ^ b, len(axes)) for a, b in zip(path, path[1:]))


def expected(ok, detail):
    if not ok:
        raise ValueError(detail)


def references():
    pins = {}
    def read(file):
        raw = file.read_bytes()
        pins[file.relative_to(HERE.parent).as_posix()] = sha256(raw).hexdigest()
        return json.loads(raw)

    endpoints = read(R248 / "endpoint94.json")["records"]
    audit = read(R248 / "aggregate.json")
    attain = read(R248 / "attainers.json")["records"]
    opposite = {r["class_id"]: r for r in read(R248 / "opposite-audit.json")["classes"]}
    audited = {tuple(r["case"]): r for r in audit["endpoint94"]}
    expected(audit["attainers"]["complete"] and audit["attainers"]["labelled"] == 25, "Attainer audit is incomplete")
    seeds, root_bounds = {}, {}
    for row in endpoints:
        i, end = row["case"]
        path = row["rooted_parent"]
        key = shape(path)
        check_path(path)
        expected(len(path) == 97 and path[0] == 0, "Unexpected seed")
        if end == 0:
            rec, = [r for r in attain if r["class_id"] == i]
            expected(audited[i, end]["verified_bank_witnesses"] == 5 and rec["status"] == "exhausted"
                     and len(rec["paths"]) == 5, "Missing five attaining partners")
            seeds[key] = path
            bounds = (94, 94)
        else:
            bounds = (opposite[i]["lower"], opposite[i]["upper"])
        root_bounds[oriented_word(path)] = dict(source="248", lower=bounds[0], upper=bounds[1])
    expected(len(seeds) == 5 and len(root_bounds) == 10, "Expected five seed shapes and ten distinct ends")

    legacy = read(R253 / "closure.json")["paths"]
    parity = read(R254 / "parity-families.json")["shapes"]
    for row in read(R254 / "aggregate.json")["cases"]:
        path = row["parent"]
        expected(len(path) == 97 and shape(path) == row["shape"], "Round 254 parent differs")
        root_bounds[oriented_word(path)] = dict(source="254", lower=row["partner_edges"], upper=row["partner_upper"])

    components = read(R253 / "relay-incidence.json")["components"]
    six = set(components["69"]["shapes"])
    four = set(components["99"]["shapes"])
    expected(len(six) == 6 and set(seeds) < six and len(four) == 4, "Unexpected earlier components")
    core = set(read(R252 / "census-68.json")["all_ids"])
    replay = read(R252 / "replay-68-192.json")
    expected(replay["all_excluded"] and len(core) == 63 and four | six <= core, "Earlier census differs")
    transported = read(R253 / "transports.json")
    by_shape = defaultdict(set)
    for row in transported["results"]:
        if row["witnesses"]:
            by_shape[row["shape"]].add(row["end"])
    expected(len(by_shape) == 18 and all(ends == {0, 1} for ends in by_shape.values()), "Transport coverage differs")
    known = set(legacy) | set(parity)
    excluded = core | set(by_shape) | set(parity)
    expected(len(known) == 241 and len(excluded) == 89 and excluded <= known, "Earlier inventory differs")
    for file in (Path(__file__), HERE / "replay_exchange.cs", HERE / "replay_exchange.py", R252 / "replay_core.py"):
        pins[file.relative_to(HERE.parent).as_posix()] = digest(file)
    pins["csc.exe"] = digest(CSC)
    return seeds, parity[SEED], known, excluded, six, four, root_bounds, pins


def expand(exe, path):
    side = set(path[1::2])
    candidates = {v for v in range(256) if v.bit_count() % 2 == path[1].bit_count() % 2} - side
    all_cases = {(r, a) for r in side for a in candidates} | {(-1, -1)}
    expected(len(all_cases) == 3841, "Wrong side partition")
    run = subprocess.run([str(exe)], input=",".join(map(str, sorted(side))) + "\n", text=True,
                         capture_output=True, check=True)
    cases, counts, labelled, first = {}, Counter(), set(), {}
    for line in run.stdout.splitlines():
        kind, removed, added, *values = line.split()
        r, a = int(removed), int(added)
        expected((r, a) in all_cases, "Unexpected replacement")
        if kind == "S":
            cycles, n = map(int, values)
            expected((r, a) not in cases and 0 <= cycles <= n, "Repeated or inconsistent case")
            cases[r, a] = n
        else:
            expected(kind == "P" and len(values) == 1, "Unexpected native output")
            p = tuple(map(int, values[0].split(",")))
            expected(len(p) == 97 and p[0] < p[-1] and p not in labelled, "Repeated or incorrectly oriented path")
            check_path(p)
            target = side if r == -1 else side - {r} | {a}
            expected(set(p[1::2]) == target, "Incorrect parity exchange")
            labelled.add(p)
            counts[r, a] += 1
            first.setdefault(shape(p), (r, a, list(p)))
    expected(cases.keys() == all_cases and all(n == counts[k] for k, n in cases.items()), "Incomplete side inventory")
    expected(tuple(min(path, path[::-1])) in labelled, "Missing unchanged parent")
    detail = dict(outgoing=sorted(first),side_classes=len(cases),nonempty=sum(bool(n) for n in cases.values()),
                  labelled=len(labelled),multiplicities=dict(Counter(cases.values())),
                  enumeration_sha256=sha256(run.stdout.encode("ascii")).hexdigest())
    return first, detail


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--limit", type=int, default=10000, help="Maximum additional parents to expand in this call")
    cli.add_argument("--seconds", type=float, default=120, help="Stop starting new parents after this time")
    cli.add_argument("--focus", action="store_true", help="Start from the Round 254 e6e522b8 arm")
    args = cli.parse_args()
    expected(args.limit > 0 and args.seconds > 0, "Positive limits required")
    seeds, focus, known, excluded, six, four, root_bounds, pins = references()
    seeds_of_191 = set(seeds)
    if args.focus:
        seeds = {SEED: focus}
    dest = HERE / ("focus-closure.json" if args.focus else "attainer-closure.json")
    ids = list(sorted(seeds))
    data = json.loads(dest.read_bytes()) if dest.exists() else dict(
        pins=pins, seeds=ids, paths={k: seeds[k] for k in ids}, discovery={k: dict(depth=0) for k in ids},
        order=ids.copy(), expanded={}, started_utc=now(), runs=[])
    expected(data["pins"] == pins and data["seeds"] == ids, "Checkpoint inputs differ")

    def save():
        data["pending"] = [k for k in data["order"] if k not in data["expanded"]]
        data["closed"] = not data["pending"]
        data["outside_previous"] = sorted(set(data["paths"])-known)
        data["earlier_six_component"] = sorted(set(data["paths"]) & six)
        ceilings = {}
        for k, p in data["paths"].items():
            rows = []
            for end, order in enumerate((p, p[::-1])):
                bound = root_bounds.get(oriented_word(order))
                if bound is None:
                    if k in four or k in six - seeds_of_191:
                        bound = dict(source="253/small components", upper=93)
                    elif k in excluded:
                        bound = dict(source="252 to 254/192 exclusions", upper=94)
                rows.append(dict(end=end, root=order[0], partner_bound=bound,
                                 target_192="excluded" if bound is not None and bound["upper"] < 95 else "unresolved"))
            ceilings[k] = rows
        data["rooted_status_through_254"] = ceilings
        data["updated_utc"] = now()
        pending = dest.with_suffix(".pending")
        pending.write_text(json.dumps(data, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
        pending.replace(dest)

    start = monotonic()
    current_run = dict(started_utc=now(), limit=args.limit, seconds_limit=args.seconds, processed=0)
    data["runs"].append(current_run)
    with TemporaryDirectory(prefix="snake255-closure-") as tmp:
        exe = Path(tmp) / "Exchange.exe"
        subprocess.run([str(CSC), "/nologo", "/optimize+", "/out:"+str(exe), str(HERE / "replay_exchange.cs")],
                       check=True, capture_output=True, timeout=45)
        cursor = 0
        while cursor < len(data["order"]):
            key = data["order"][cursor]
            cursor += 1
            if key in data["expanded"]:
                continue
            if current_run["processed"] >= args.limit or monotonic()-start >= args.seconds:
                break
            begin = monotonic()
            new, detail = expand(exe, data["paths"][key])
            for child in sorted(new):
                if child in data["paths"]:
                    continue
                removed, added, vertices = new[child]
                data["paths"][child] = vertices
                data["order"].append(child)
                data["discovery"][child] = dict(parent=key, removed=removed, added=added,
                                                depth=data["discovery"][key]["depth"]+1)
            detail["seconds"] = monotonic()-begin
            data["expanded"][key] = detail
            current_run["processed"] += 1
            current_run["seconds"] = monotonic()-start
            save()
            print(key[:10], "labelled", detail["labelled"], "shapes", len(new),
                  "expanded", len(data["expanded"]), "pending", len(data["pending"]), flush=True)
    current_run.update(finished_utc=now(), seconds=monotonic()-start)
    save()
    print("closed", data["closed"], "shapes", len(data["paths"]), "outside previous", len(data["outside_previous"]))


if __name__ == "__main__":
    main()
