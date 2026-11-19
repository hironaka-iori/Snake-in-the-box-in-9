"""Lift all one-vertex exchanges of the unique congruent complementary Q7 middle."""
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess

import cert_replay as audit
import lifts


HERE = Path(__file__).resolve().parent
LEDGER = HERE / "near-lifts.json"
INPUT_PINS = {
    "q7-census.json": "b6d8335fe9fe9e8fd7a945c485d3eacc07e8094aab551e10f50bce62f570866b",
    "q7-census-paths.txt": "7fd4c6cec8cc3397557653ad2bdd926d6055cff9696e97e63fc76b1db926f0c4",
    "orbit.json": "fbed9e6a730c1f0cc0ba6b2b1c2b893620674edddc095ef3ad798049d86ffd96",
}


def save(file, data):
    tmp = file.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
    tmp.replace(file)


def families():
    for name, expected in INPUT_PINS.items():
        audit.require(audit.digest(HERE/name) == expected, ("Final input hash", name))
    census = json.loads((HERE/"q7-census.json").read_bytes())
    orbit = json.loads((HERE/"orbit.json").read_bytes())
    first, reference = orbit["first"], orbit["reference"]
    mate = set(reference)
    audit.require(census["status"] == "complete" and census["all_roots_complete"] and
                  census["first"] == first and census["lengths"] == {"47": 1108, "48": 5} and
                  census["paths_sha256"] == INPUT_PINS["q7-census-paths.txt"] and
                  census["pins"]["orbit.json"] == INPUT_PINS["orbit.json"], "Incomplete census")
    audit.require(len(orbit["disjoint"]) == 1 and set(orbit["disjoint"][0]["path"]) == mate,
                  "Congruent mate differs")
    audit.verify(first, 7)
    audit.verify(reference, 7)
    seen = set()
    histogram = Counter()
    close = []
    n48 = 0
    for line in (HERE/"q7-census-paths.txt").read_text(encoding="ascii").splitlines():
        path = list(map(int, line.split()))
        audit.verify(path, 7)
        points = frozenset(path)
        audit.require(points.isdisjoint(first) and points not in seen, "Duplicate or inadmissible path")
        seen.add(points)
        if len(path) == 49:
            n48 += 1
            continue
        audit.require(len(path) == 48 and path[0].bit_count() % 2 == 0, "Noncanonical 47-edge path")
        removed, added = mate - points, points - mate
        audit.require(len(removed) == len(added), "Unequal exchange sizes")
        histogram[len(removed)] += 1
        if len(removed) == 1:
            close.append((path, next(iter(removed)), next(iter(added))))
    audit.require(sum(histogram.values()) == 1108 and n48 == 5 and histogram[0] == 1 and
                  histogram[1] == len(close) == 4, "Incorrect one-exchange coverage")
    rows = []
    for i, (path, removed, added) in enumerate(sorted(close)):
        sites = [q for q in range(128) if q not in first[1:-1] and q not in path[1:-1]]
        audit.require(len(sites) == 36, "Incorrect possible joining vertices")
        rows.append(dict(index=i, middle=path, removed=removed, inserted=added, sites=sites))
    return first, reference, dict(sorted(histogram.items())), rows


def witness_check(path, lengths, first, middle, q, fixed, chosen):
    audit.verify(path, 9)
    selected = set(path)
    a, b = lengths
    audit.require(fixed <= selected <= fixed | set(chosen) and
                  len(path)-1 == a+b+1 >= 192 and max(a, b) <= 98 and
                  sum(v < 256 for v in selected) == a+1 and
                  {v for v in selected if v < 256 and v+256 in selected} == {q},
                  "Lift cardinality, domain, or crossing mismatch")
    for x, mid in enumerate((first, middle)):
        actual = {v & 127 for v in selected if v >> 7 == 1+2*x}
        audit.require(actual == set(mid), "Incorrect selected middle")
    decoded, cycles = lifts.inspect(selected, [first, middle], q, a, b)
    audit.require(not cycles and decoded in (path, path[::-1]), "Witness reconstruction failed")


def replay(data, families_meta):
    witness = None
    reports = []
    with TemporaryDirectory(prefix="q9-near-middle-replay-") as tmp:
        folder = Path(tmp)
        checker = folder/"VerifyLrat.exe"
        filename = folder/"case.cnf"
        subprocess.run([str(audit.COMPILER), "/nologo", "/optimize+", "/out:"+str(checker), str(audit.CHECKER)],
                       check=True, capture_output=True, timeout=60)
        for info, row in zip(families_meta, data["families"]):
            for k, v in info.items():
                audit.require(row[k] == v, ("Incorrect family", k))
            sites = row["sites"]
            results = row["results"]
            audit.require([r["q"] for r in results] == sites[:len(results)], "Incorrect site coverage")
            family_reports = []
            counts = Counter()
            for case in results:
                q, status = case["q"], case["status"]
                audit.require(witness is None and status in ("excluded", "witness", "unknown") and
                              case["attempts"], "Invalid case after witness or missing attempts")
                cnf, chosen, fixed = lifts.model([data["first"], row["middle"]], q, 192)
                proof = None
                cycle_count = 0
                for j, attempt in enumerate(case["attempts"]):
                    audit.require(cnf.save(filename) == attempt["cnf_sha256"], "Regenerated CNF differs")
                    outcome = attempt["outcome"]
                    last = j+1 == len(case["attempts"])
                    if outcome == "disconnected":
                        audit.require(attempt["cycles"] and (not last or status == "unknown"), "Bad cycle step")
                        for cycle in attempt["cycles"]:
                            cnf.clauses.append(audit.cycle_cut(cycle, chosen, fixed))
                            cycle_count += 1
                    elif outcome == "UNSAT":
                        tag = "lift-proofs/near%d-q%d.lrat.gz" % (row["index"], q)
                        audit.require(last and status == "excluded" and attempt["proof"] == tag, "Bad proof tag")
                        proof = audit.replay_proof(attempt, "proof", filename, checker)
                    elif outcome == "connected":
                        audit.require(last and status == "witness", "Bad witness status")
                        witness = case["path"]
                        witness_check(witness, case["arm_lengths"], data["first"], row["middle"], q, fixed, chosen)
                    else:
                        audit.require(last and outcome == "timeout" and status == "unknown", "Bad terminal step")
                audit.require((proof is not None) == (status == "excluded"), "Missing LRAT proof")
                checked = ("checked_exclusion" if proof and proof["accepted"] else
                           "unverified_exclusion" if proof else status)
                counts[checked] += 1
                family_reports.append(dict(q=q, result=checked, cycle_cuts=cycle_count, proof=proof))
            audit.require(witness is not None or len(results) == len(sites), "Unqueried sites without witness")
            reports.append(dict(index=row["index"], removed=row["removed"], inserted=row["inserted"],
                                requested=len(sites), unqueried=len(sites)-len(results), counts=counts,
                                checked_family_exclusion=counts["checked_exclusion"] == len(sites),
                                sites=family_reports))
        executable_hash = audit.digest(checker)
    audit.require(len(reports) == len(families_meta) == 4 and data["witness"] == witness, "Incomplete families")
    output = dict(near_lifts_sha256=audit.digest(LEDGER), census_pins=INPUT_PINS,
                  checker_source_sha256=audit.digest(audit.CHECKER), checker_executable_sha256=executable_hash,
                  compiler_sha256=audit.digest(audit.COMPILER), source_sha256=audit.digest(Path(__file__)),
                  per_family=reports, witness_edges=len(witness)-1 if witness else None)
    save(HERE/"near-replay.json", output)
    if any(r["counts"]["unverified_exclusion"] for r in reports):
        raise RuntimeError("At least one saved LRAT was not accepted")
    for r in reports:
        print("family", r["index"], "remove", r["removed"], "insert", r["inserted"], dict(r["counts"]), flush=True)


def main():
    first, reference, histogram, meta = families()
    srcs = [Path(__file__), HERE/"lifts.py", HERE/"cert_replay.py", lifts.PREV/"ceiling.py",
            lifts.PREV/"replay.py", lifts.PREV/"free_outer.py", lifts.PREV/"refine_outer.py",
            HERE.parent/"243-coil-opening/arc_sat.py", lifts.SOLVER]
    pins = {**INPUT_PINS, **{p.name: audit.digest(p) for p in srcs}}
    prior = json.loads((HERE/"lifts.json").read_bytes())
    audit.require(pins["lifts.py"] == prior["source_sha256"] and
                  pins[lifts.SOLVER.name] == prior["solver_sha256"], "Changed lift solver or implementation")
    base = dict(target=192, budget=1.0, first=first, reference=reference, pins=pins,
                deletion_histogram={str(k): v for k, v in histogram.items()},
                ordering="Lexicographic order of the census paths, each starting at its even endpoint.")
    if LEDGER.exists():
        data = json.loads(LEDGER.read_bytes())
        audit.require(all(data[k] == v for k, v in base.items()) and len(data["families"]) == 4,
                      "Checkpoint inputs differ")
    else:
        data = dict(**base, families=[dict(**m, results=[]) for m in meta], witness=None)
        save(LEDGER, data)
    with TemporaryDirectory(prefix="q9-near-middle-lifts-") as tmp:
        for row, info in zip(data["families"], meta):
            audit.require(all(row[k] == v for k, v in info.items()), "Changed checkpoint family")
            sites = row["sites"]
            done = row["results"]
            audit.require([r["q"] for r in done] == sites[:len(done)], "Changed checkpoint sites")
            if data["witness"] is not None:
                continue
            for q in sites[len(done):]:
                result = lifts.decide([first, row["middle"]], q, 192, Path(tmp),
                                      "near%d-q%d" % (row["index"], q), 1.0)
                done.append(dict(q=q, **result))
                if result["status"] == "witness":
                    data["witness"] = result["path"]
                save(LEDGER, data)
                if data["witness"] is not None:
                    break
            print("family", row["index"], "queried", len(done), "of", len(sites), flush=True)
    replay(data, meta)


if __name__ == "__main__":
    main()
