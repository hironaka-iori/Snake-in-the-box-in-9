"""Combine endpoint-scoped checks for triples with one odd frequency."""

import argparse
import json
from pathlib import Path

from q9_audit_distance_seven_profiles import DISTANCE_TAG, audit


def cover(path):
    baseline = json.loads(path.read_text())
    counts = baseline["counts"]
    assert sum(value % 2 for value in counts) == 1
    # Odd path length leaves distances 1, 3, 5, 7, 9.
    # Distance 1 is a chord and distance 9 would make all frequencies odd.
    distances = (3, 5, 7)
    remaining = set()
    evidence = {}
    for distance in distances:
        case = audit(path, distance)
        tag = DISTANCE_TAG[distance]
        remaining.update(case["remaining"])
        evidence[str(distance)] = case[f"{tag}_replays"]
    checked = sorted(set(baseline["remaining"]) - remaining)
    full_q9_verified = baseline["full_q9_verified"] + len(checked)
    assert (baseline["excluded_by_local"] + full_q9_verified + len(remaining)
            == baseline["initial_orbits"])
    return dict(status="MIXED_ENDPOINT_BRANCH_CLOSED" if not remaining else "MIXED_ENDPOINT_PARTIAL_COVERAGE",
                counts=counts, initial_orbits=baseline["initial_orbits"],
                excluded_by_local=baseline["excluded_by_local"], full_q9_verified=full_q9_verified,
                endpoint_distances=list(distances), source=path.name,
                exact_distance_exclusions=checked, remaining=sorted(remaining), evidence=evidence)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    result = cover(args.baseline)
    with args.output.open("x") as out:
        json.dump(result, out, indent=2)
        out.write("\n")
    print(json.dumps(dict(counts=result["counts"], exact_exclusions=len(result["exact_distance_exclusions"]),
                          remaining=len(result["remaining"]))))
