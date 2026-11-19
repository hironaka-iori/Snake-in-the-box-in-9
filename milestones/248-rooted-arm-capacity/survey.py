"""Search the sixteen previously unresolved rooted arms with free endpoints."""
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic, sleep
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "247-relative-middle-placements"
sys.path.insert(0, str(PREVIOUS))
import partner


def save_json(path, record):
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(record, separators=(",", ":")) + "\n", encoding="utf-8", newline="\n")
    for retry in range(8):
        try:
            temp.replace(path)
            return
        except PermissionError:
            if retry == 7:
                raise
            sleep(.15)


def cases():
    source = PREVIOUS / "partner-children-summary.json"
    summary = json.loads(source.read_bytes())
    if summary["pending"] or summary["replay_error"] or summary["ledger_sha256"] != partner.digest(PREVIOUS / "partner-children.json"):
        raise ValueError("Incomplete predecessor")
    rows = [(c["class_id"], c["endpoint"], s) for c in summary["endpoint_cases"] for s in c.get("unknown", [])]
    if len(set(rows)) != len(rows) or len(rows) != 16:
        raise ValueError("Unexpected open root coverage")
    return sorted(rows, key=lambda r: (sum(k[:2] == r[:2] for k in rows), r))


def probe(parent, prefix, folder, seconds):
    cnf, chosen = partner.encode(parent, prefix)
    deadline = monotonic() + seconds
    attempts = []
    while monotonic() < deadline:
        path = folder / "root.cnf"
        digest = cnf.save(path)
        try:
            result = subprocess.run([str(partner.SOLVER), "-q", "--seed=1", str(path)],
                                    capture_output=True, timeout=max(.01, deadline - monotonic()))
        except subprocess.TimeoutExpired:
            return dict(status="open", attempts=attempts, final_cnf=digest)
        if result.returncode == 20 and b"s UNSATISFIABLE" in result.stdout:
            return dict(status="native_unsat", attempts=attempts, final_cnf=digest)
        if result.returncode != 10 or b"s SATISFIABLE" not in result.stdout:
            raise RuntimeError((result.returncode, result.stderr[-150:]))
        truth = {int(v) for line in result.stdout.splitlines() if line.startswith(b"v ") for v in line.split()[1:] if int(v)>0}
        selected = {v for v, lit in chosen.items() if lit in truth}
        suffix, joined, cycles = partner.extract(parent, prefix, selected)
        if joined is not None:
            return dict(status="witness", attempts=attempts, final_cnf=digest, partner=suffix, joined=joined)
        attempts.append(dict(cnf=digest, cycles=cycles))
        for cycle in cycles:
            cnf.clauses.append(partner.cycle_clause(chosen,cycle))
    return dict(status="open", attempts=attempts)


def main():
    jobs = cases()
    arms = partner.parent_arms()
    destination = HERE / "survey.json"
    inputs = [Path(__file__), PREVIOUS/"partner.py", PREVIOUS/"partner-children-summary.json",
              partner.PREV/"comparison.json", partner.SOLVER]
    pins = {p.name:partner.digest(p) for p in inputs}
    data = json.loads(destination.read_bytes()) if destination.exists() else dict(pins=pins,seconds=7,records=[])
    if data["pins"] != pins or [r["case"] for r in data["records"]] != [list(j) for j in jobs[:len(data["records"])]]:
        raise ValueError("Prior survey does not match the inputs")
    with TemporaryDirectory(prefix="snake248-survey-") as tmp:
        for i,e,s in jobs[len(data["records"]):]:
            if any(r["status"]=="witness" for r in data["records"]):
                break
            parent = partner.rooted_parent(arms[i],e)
            record = probe(parent,[0,s],Path(tmp),data["seconds"])
            data["records"].append(dict(case=[i,e,s],**record))
            save_json(destination,data)
            print(i,e,s,record["status"],flush=True)


if __name__=="__main__":
    main()
