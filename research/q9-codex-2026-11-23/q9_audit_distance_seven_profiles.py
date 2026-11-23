"""Audit frequency projections with proofs scoped to one endpoint distance."""

import argparse
import json
from pathlib import Path


DISTANCE_TAG = {3: "distance_three", 5: "distance_five", 7: "distance_seven"}


def checked_replays(prefix, orbit_count, counts, distance):
    verified = set()
    evidence = []
    for path in sorted(prefix.parent.glob(f"{prefix.name}_d{distance}_*_replay.log")):
        rows = [json.loads(line) for line in path.read_text().splitlines(keepends=True)
                if line.endswith("\n")]
        if not rows or rows[-1]["status"] != f"D{distance}_REPLAY_DONE":
            continue
        summary = rows[-1]
        assert all(row["status"] == f"VERIFIED_D{distance}_Q9" for row in rows[:-1])
        indices = {row["index"] for row in rows[:-1]}
        unresolved = set(summary["unresolved"])
        assert len(indices) == len(rows) - 1 == summary["verified"]
        assert not indices & unresolved and len(indices | unresolved) == summary["tested"]
        assert all(0 <= index < orbit_count for index in indices | unresolved)
        selected = path.with_name(path.name.removesuffix("_replay.log") + ".selection.json")
        selection = json.loads(selected.read_text())
        assert selection["status"] == "VERIFIED" and selection["endpoint_distance"] == distance
        assert selection["counts"] == counts
        assert indices | unresolved == set(selection["indices"])
        verified.update(indices)
        evidence.append(path.name)
    return verified, evidence


def audit(path, distance):
    baseline = json.loads(path.read_text())
    counts = baseline["counts"]
    assert sum(n % 2 for n in counts) == 1
    assert baseline["status"] == "PARTIAL_COVERAGE_VERIFIED" and baseline["projection_verified"]
    pending = set(baseline["remaining"])
    assert len(pending) == len(baseline["remaining"])
    orbit_count = baseline["initial_orbits"]
    assert baseline["excluded_by_local"] + baseline["full_q9_verified"] + len(pending) == orbit_count
    prefix = path.with_name(path.name.removesuffix("_partial_coverage_audit.json"))
    checked, evidence = checked_replays(prefix, orbit_count, counts, distance)
    tag = DISTANCE_TAG[distance]
    return dict(counts=counts, projection_orbits=orbit_count, source=path.name,
                remaining=sorted(pending - checked),
                **{f"{tag}_exclusions": sorted(checked & pending), f"{tag}_replays": evidence})


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("baselines", type=Path, nargs="+")
    parser.add_argument("--distance", type=int, choices=tuple(DISTANCE_TAG), default=7)
    args = parser.parse_args()
    cases = [audit(path, args.distance) for path in args.baselines]
    tag = DISTANCE_TAG[args.distance]
    result = dict(status=f"{tag.upper()}_PROJECTION_AUDIT", endpoint_distance=args.distance, cases=cases)
    with args.output.open("x") as output:
        json.dump(result, output, indent=2)
        output.write("\n")
    print(json.dumps([dict(counts=case["counts"], excluded=len(case[f"{tag}_exclusions"]),
                           remaining=len(case["remaining"])) for case in cases]))
