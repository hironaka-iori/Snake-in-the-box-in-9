"""Split each unresolved 96-edge parent case over every possible first step."""
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import sys

import partner
import partner_replay


HERE = Path(__file__).resolve().parent
LEDGER = HERE / "partner-children.json"


def atomic_json(file, data):
    tmp = file.with_suffix(".tmp")
    tmp.write_text(json.dumps(data, separators=(",", ":"))+"\n", encoding="utf-8", newline="\n")
    tmp.replace(file)


def redirected_replay(ledger):
    saved = sys.argv
    try:
        sys.argv = [str(HERE/"partner_replay.py"), str(ledger)]
        partner_replay.main()
    finally:
        sys.argv = saved
    receipt = ledger.with_name(ledger.stem+"-lrat.json")
    replay = json.loads(receipt.read_bytes())
    if replay["source_sha256"] != partner.digest(ledger):
        raise ValueError("Stale child LRAT receipt")
    return replay


def key(row):
    return row["class_id"], row["endpoint"], tuple(row["prefix"])


def status_rows(original, coverage, results, checked, original_checked):
    lookup = {key(r): r for r in results}
    groups = {(g["class_id"], g["endpoint"]): g for g in coverage}
    summary = []
    for r in original["records"]:
        c = (r["class_id"], r["endpoint"])
        if c not in groups:
            status = "checked_unrestricted_exclusion" if c in original_checked else r["status"]
            summary.append(dict(class_id=c[0], endpoint=c[1], status=status))
            continue
        firsts = groups[c]["first_steps"]
        buckets = {s: [] for s in ("pending", "unknown", "witness", "solver_unsat", "checked")}
        for first in firsts:
            case = (c[0], c[1], (0, first))
            row = lookup.get(case)
            status = "pending" if row is None else row["status"]
            buckets[status].append(first)
            if case in checked:
                buckets["checked"].append(first)
        if buckets["witness"]:
            status = "verified_witness"
        elif len(buckets["checked"]) == len(firsts):
            status = "checked_exclusion_by_all_first_steps"
        elif len(buckets["solver_unsat"]) == len(firsts):
            status = "all_first_steps_solver_unsat"
        elif buckets["pending"]:
            status = "incomplete"
        else:
            status = "open"
        summary.append(dict(class_id=c[0], endpoint=c[1], status=status, first_steps=firsts, **buckets))
    return summary


def main():
    source = HERE/"partners.json"
    original = json.loads(source.read_bytes())
    original_receipt = HERE/"partners-lrat.json"
    replay = json.loads(original_receipt.read_bytes())
    if original["pending"] or replay["source_sha256"] != partner.digest(source):
        raise ValueError("Expected the completed unrestricted survey and its matching replay")
    pinned = [HERE/"partner.py", partner.PREV/"arm-structure.json", partner.PREV/"comparison.json",
              partner.PREV/"free_outer.py", partner.SOURCE/"arc_sat.py", partner.SOLVER]
    if {p.name: partner.digest(p) for p in pinned} != original["pins"]:
        raise ValueError("Original solver, source or input pins differ")
    original_checked = {(r["class_id"], r["endpoint"]) for r in replay["cases"]}
    arms = partner.parent_arms()
    expected = {(i, e) for i in arms for e in (0, 1)}
    cases = {(r["class_id"], r["endpoint"]): r for r in original["records"]}
    if len(cases) != len(original["records"]) or set(cases) != expected or len(expected) != 10:
        raise ValueError("Unrestricted endpoint coverage differs")
    coverage = []
    for c in sorted(cases):
        row = cases[c]
        if row["status"] != "unknown":
            continue
        if row["prefix"] != [0] or row["seed"] != 0 or row["budget_seconds"] != 2:
            raise ValueError("Unexpected original query")
        parent = partner.rooted_parent(arms[c[0]], c[1])
        firsts = [1 << i for i in range(8) if (1 << i) not in parent]
        if len(firsts) != 7 or firsts != partner.next_vertices(parent, [0]):
            raise ValueError("First-step coverage mismatch")
        coverage.append(dict(class_id=c[0], endpoint=c[1], rooted_parent=parent, first_steps=firsts))
    jobs = [(g, v) for g in coverage for v in g["first_steps"]]
    keys = [(g["class_id"], g["endpoint"], (0, v)) for g, v in jobs]
    pins = {p.name: partner.digest(p) for p in
            (source, original_receipt, Path(__file__), HERE/"partner_replay.py", partner.PREV/"VerifyLrat.cs")}
    if LEDGER.exists():
        ledger = json.loads(LEDGER.read_bytes())
        rows = ledger["records"]
        if (ledger["pins"] != pins or ledger["coverage"] != coverage or ledger["requested"] != len(jobs)
                or [key(r) for r in rows] != keys[:len(rows)] or ledger["pending"] != len(jobs)-len(rows)
                or any(r["seed"] != 0 or r["budget_seconds"] != 2 or r["initial_cycles"] for r in rows)):
            raise ValueError("Existing child ledger does not match its original inputs or coverage")
    else:
        rows = []
        ledger = dict(pins=pins, coverage=coverage, requested=len(jobs), pending=len(jobs),
                      budget_seconds=2, seed=0, records=rows)
        atomic_json(LEDGER, ledger)
    with TemporaryDirectory(prefix="q8-partner-children-") as tmp:
        for g, v in jobs[len(rows):]:
            if any(r["status"] == "witness" for r in rows):
                break
            result = partner.decide(g["rooted_parent"], [0, v], Path(tmp), seconds=2, seed=0)
            rows.append(dict(class_id=g["class_id"], endpoint=g["endpoint"], **result))
            ledger["pending"] = len(jobs)-len(rows)
            atomic_json(LEDGER, ledger)
            print("Arm", g["class_id"], "endpoint", g["endpoint"], "first", v, result["status"], flush=True)

    summary_file = HERE/"partner-children-summary.json"
    def summarize(checked, failure=None):
        atomic_json(summary_file, dict(ledger_sha256=partner.digest(LEDGER), original_pins=pins,
                    replay_error=failure, pending=ledger["pending"],
                    endpoint_cases=status_rows(original, coverage, rows, checked, original_checked)))
    summarize(set())
    try:
        child_replay = redirected_replay(LEDGER)
    except (ValueError, OSError, RuntimeError) as e:
        summarize(set(), str(e))
        raise
    checked = {key(r) for r in child_replay["cases"]}
    if checked != {key(r) for r in rows if r["status"] == "solver_unsat"}:
        raise ValueError("Child LRAT receipt does not cover the recorded solver exclusions")
    summarize(checked)
    for row in status_rows(original, coverage, rows, checked, original_checked):
        print(row["class_id"], row["endpoint"], row["status"], "unknown firsts", row.get("unknown", []))


if __name__ == "__main__":
    main()
