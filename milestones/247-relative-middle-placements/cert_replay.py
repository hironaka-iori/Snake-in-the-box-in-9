"""Check the complementary-path and outer-lift records, CNFs, cuts and LRAT files."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import gzip
import json
import subprocess

import complementary
import lifts
from placements import verify
from replay import cycle_cut


HERE = Path(__file__).resolve().parent
PREVIOUS = complementary.PREVIOUS
CHECKER = PREVIOUS / "VerifyLrat.cs"
COMPILER = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def replay_proof(row, field, filename, executable):
    compressed = HERE / row[field]
    raw = sha256()
    size = 0
    with gzip.open(compressed, "rb") as file:
        for chunk in iter(lambda: file.read(65536), b""):
            size += len(chunk)
            raw.update(chunk)
    require(raw.hexdigest() == row["lrat_sha256"], ("LRAT hash", compressed))
    require(size > 0 and size == row.get("lrat_bytes", size), ("LRAT size", compressed))
    try:
        run = subprocess.run([str(executable), str(filename), str(compressed)],
                             capture_output=True, timeout=60)
        statement = run.stdout.decode("ascii").strip()
        accepted = run.returncode == 0 and statement.startswith("VERIFIED UNSAT ")
        message = statement if accepted else run.stderr.decode("ascii", "replace").strip()
    except subprocess.TimeoutExpired:
        accepted, message = False, "checker timeout after 60 seconds"
    return dict(cnf_sha256=row["cnf_sha256"], proof=row[field], raw_sha256=raw.hexdigest(),
                raw_bytes=size, accepted=accepted, checker_report=message)


def complementary_paths(row, forbidden):
    length, majority = row["length"], row["majority"]
    paths = set()
    for path in row["paths"] + row["additional_verified_subpaths"]:
        verify(path, 7)
        require(len(path) == length + 1 and forbidden.isdisjoint(path), "Invalid complementary path")
        for parity in (0, 1):
            count = sum(v.bit_count() % 2 == parity for v in path)
            require(count == (length + 1) // 2 + int(parity == majority), "Invalid path parity")
        points = frozenset(path)
        require(points not in paths, "Duplicate complementary path set")
        paths.add(points)
    return {frozenset(p) for p in row["paths"]}


def complementary_cases(data, filename, executable):
    orbit = json.loads((HERE / "orbit.json").read_bytes())
    first = data["first"]
    require((first, data["reference"]) == (orbit["first"], orbit["reference"]), "Changed orbit input")
    for path in (first, data["reference"]):
        verify(path, 7)
        require(len(path) == 48, "Wrong reference length")
    forbidden = set(first)
    require(forbidden.isdisjoint(data["reference"]), "Intersecting reference paths")
    require([(r["length"], r["majority"]) for r in data["records"]] == complementary.CASES,
            "Incomplete complementary case inventory")
    reports = []
    for row in data["records"]:
        length, majority = row["length"], row["majority"]
        paths = complementary_paths(row, forbidden)
        blocked_paths = set()
        blocks = row["blocks"]
        cnf, chosen = complementary.encode(first, length, majority)
        cuts = []
        for block in blocks:
            vertices = block["vertices"]
            if block["kind"] == "path":
                key = frozenset(vertices)
                require(len(vertices) == len(key) and key in paths and key not in blocked_paths,
                        "Path clause lacks a distinct full-length witness")
                blocked_paths.add(key)
                cuts.append([-chosen[v] for v in vertices])
            else:
                require(block["kind"] == "cycle", "Unknown complementary block")
                cuts.append(cycle_cut(vertices, chosen, set()))
        require(blocked_paths == paths, "Mismatch between full-path witnesses and their clauses")
        attempts = row["attempts"]
        position = 0
        proof = None
        exhausted = row["status"] == "native_exhaustion"
        require(exhausted or row["status"] in ("unknown_path_limit", "unknown_time_limit"),
                "Unrecognized complementary case status")
        require(not exhausted or not row["additional_verified_subpaths"], "Unblocked path in exhausted case")
        for index, attempt in enumerate(attempts):
            start = attempt["blocks_at_query"]
            stop = attempts[index + 1]["blocks_at_query"] if index + 1 < len(attempts) else len(blocks)
            require(position <= start <= stop <= len(blocks), "Invalid complementary block index")
            if index == 0:
                require(all(b["kind"] == "path" for b in blocks[:start]), "Invalid initial path clauses")
            cnf.clauses.extend(cuts[position:start])
            position = start
            require(cnf.count == attempt["variables"] and len(cnf.clauses) == attempt["clauses"]
                    and cnf.save(filename) == attempt["cnf_sha256"], "Complementary DIMACS changed")
            kinds = [b["kind"] for b in blocks[start:stop]]
            result = attempt["result"]
            if result == "verified_path":
                require(kinds == ["path"], "Incorrect added path clause")
            elif result == "disconnected":
                require(kinds and all(k == "cycle" for k in kinds), "Incorrect added cycle clauses")
            elif result == "timeout":
                require(not kinds, "Timeout added a clause")
            else:
                require(result == "UNSAT" and not kinds and index == len(attempts) - 1 and exhausted,
                        "Unexpected complementary proof location")
                proof = replay_proof(attempt, "lrat", filename, executable)
        require((proof is not None) == exhausted, "Missing complementary proof")
        reports.append(dict(length=length, majority=majority, source_status=row["status"],
                            verified_paths=len(paths), additional_paths=len(row["additional_verified_subpaths"]),
                            path_clauses=len(blocked_paths), cycle_clauses=len(cuts) - len(blocked_paths),
                            regenerated_cnfs=len(attempts), proof=proof))
    return reports


def lift_cases(data, complementary_data, filename, executable):
    target = data["target"]
    first = complementary_data["first"]
    partners = sorted(p for r in complementary_data["records"] if r["length"] == 48 for p in r["paths"])
    require(target == 192 and data["first"] == first, "Incorrect lift inputs")
    reports = []
    witness = None
    for index, row in enumerate(data["rows"]):
        middle = row["middle"]
        require(witness is None and row["index"] == index and middle == partners[index], "Incorrect lift partner")
        middles = [first, middle]
        sites = sorted(set(range(128)) - set(first[1:-1]) - set(middle[1:-1]))
        require(sites == row["sites"], "Incorrect crossing site inventory")
        for number, site in enumerate(row["results"]):
            q = site["q"]
            require(witness is None and q == sites[number], "Incorrect crossing site")
            cnf, chosen, fixed = lifts.model(middles, q, target)
            attempts = site["attempts"]
            status = site["status"]
            require(status in ("unknown", "witness", "excluded") and attempts, "Invalid lift case status")
            proof = None
            cycle_count = 0
            for j, attempt in enumerate(attempts):
                require(cnf.save(filename) == attempt["cnf_sha256"], ("Lift DIMACS changed", index, q, j))
                outcome = attempt["outcome"]
                if outcome == "disconnected":
                    require(attempt["cycles"], "No cycles in disconnected lift")
                    for cycle in attempt["cycles"]:
                        cnf.clauses.append(cycle_cut(cycle, chosen, fixed))
                        cycle_count += 1
                else:
                    require(j == len(attempts) - 1, "Nonterminal lift outcome")
                    if outcome == "UNSAT" and status == "excluded":
                        proof = replay_proof(attempt, "proof", filename, executable)
                    elif outcome == "connected" and status == "witness":
                        witness = site["path"]
                        verify(witness, 9)
                        selected = set(witness)
                        a, b = site["arm_lengths"]
                        require(fixed <= selected <= fixed | set(chosen) and max(a, b) <= 98
                                and a + b + 1 == len(witness) - 1 >= target, "Invalid lift length or ports")
                        path, _ = lifts.inspect(selected, middles, q, a, b)
                        require(path in (witness, witness[::-1]), "Witness outside claimed lift")
                    else:
                        require(outcome == "timeout" and status == "unknown", "Invalid terminal lift outcome")
            require((proof is not None) == (status == "excluded")
                    and (witness is not None) == (status == "witness"), "Incomplete lift evidence")
            reports.append(dict(index=index, q=q, source_status=status, regenerated_cnfs=len(attempts),
                                cycle_clauses=cycle_count, witness_edges=len(witness)-1 if witness else None,
                                proof=proof))
        require(witness is not None or len(row["results"]) == len(sites) or index == len(data["rows"]) - 1,
                "A completed partner row skipped crossing sites")
    require(witness == data["witness"], "Incorrect overall lift witness")
    possible = sum(len(set(range(128)) - set(first[1:-1]) - set(p[1:-1])) for p in partners)
    return reports, possible - len(reports)


def main():
    comp_file, lift_file = HERE / "complementary.json", HERE / "lifts.json"
    comp_raw, lift_raw = comp_file.read_bytes(), lift_file.read_bytes()
    comp, lift = json.loads(comp_raw), json.loads(lift_raw)
    inputs = {comp_file.name: sha256(comp_raw).hexdigest(), lift_file.name: sha256(lift_raw).hexdigest()}
    source = complementary.SOURCE
    pins = [HERE / "complementary.py", HERE / "orbit.json", PREVIOUS / "free_outer.py",
            PREVIOUS / "refine_outer.py", source / "arc_sat.py", source / "open_coil.py"]
    for p in pins:
        require(digest(p) == comp["pins"][p.name], ("Complementary source pin", p))
    require(lift["source_sha256"] == digest(HERE / "lifts.py")
            and lift["input_sha256"] == inputs[comp_file.name], "Changed lift inputs or encoder")
    with TemporaryDirectory(prefix="q9-247-replay-") as directory:
        exe = Path(directory) / "VerifyLrat.exe"
        filename = Path(directory) / "case.cnf"
        subprocess.run([str(COMPILER), "/nologo", "/optimize+", "/out:" + str(exe), str(CHECKER)],
                       check=True, capture_output=True, timeout=60)
        comp_reports = complementary_cases(comp, filename, exe)
        lift_reports, unqueried = lift_cases(lift, comp, filename, exe)
        exe_hash = digest(exe)
    proofs = [r["proof"] for r in comp_reports + lift_reports if r["proof"] is not None]
    rejected = sum(not p["accepted"] for p in proofs)
    audit_sources = pins + [Path(__file__), HERE / "lifts.py", PREVIOUS / "ceiling.py",
                            PREVIOUS / "replay.py", PREVIOUS / "placements.py", CHECKER, COMPILER]
    out = dict(inputs=inputs,
               source_sha256={p.name: digest(p) for p in audit_sources}, checker_executable_sha256=exe_hash,
               complementary=comp_reports, lifts=lift_reports, lift_statuses=Counter(r["source_status"] for r in lift_reports),
               lift_sites_unqueried=unqueried, checked_lrats=len(proofs),
               accepted_lrats=len(proofs)-rejected, rejected_lrats=rejected)
    (HERE / "cert-replay.json").write_text(json.dumps(out, separators=(",", ":")) + "\n", encoding="utf-8", newline="\n")
    print("Complementary cases", len(comp_reports), "lift sites", len(lift_reports),
          "LRAT accepted", len(proofs)-rejected, "rejected", rejected)
    if rejected:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
