"""Extend an independently verified Q9 antipodal projection audit."""

import argparse
import json
from pathlib import Path

from q9_replay_frequency_delta import run as audit
from q9_screen_monotone_seams import run as screen
from verify_q9_frequency_branch import completed_replay_records


def completed_local_replays(directory, prefix):
    for path in sorted(directory.glob(f"{prefix}_*.replay.json")):
        content=path.read_text()
        if not content.strip():
            continue
        try:
            data=json.loads(content)
        except json.JSONDecodeError:
            if content.endswith("\n"):
                raise
            continue
        if data["status"]=="VERIFIED_GEOMETRIC":
            yield path


def antipodal_replays(prefix, orbit_count):
    verified = set()
    evidence = []
    for path in sorted(prefix.parent.glob(f"{prefix.name}_antipodal_*_replay.log")):
        rows = completed_replay_records(path, "ANTIPODAL_REPLAY_DONE")
        if not rows:
            continue
        summary = rows[-1]
        assert all(row["status"] == "VERIFIED_ANTIPODAL_Q9" for row in rows[:-1])
        ids = {row["index"] for row in rows[:-1]}
        unresolved = set(summary["unresolved"])
        assert len(ids) == len(rows)-1 == summary["verified"]
        assert not ids & unresolved and len(ids | unresolved) == summary["tested"]
        assert all(0 <= index < orbit_count for index in ids | unresolved)
        verified.update(ids)
        evidence.append(path.name)
    return verified, evidence


def run(previous, table, source_geometry, destination_geometry, output, manifests):
    directory = previous.parent
    prior = json.loads(previous.read_text())
    assert prior["endpoint_distance"] == 9
    cases = []
    for case in prior["cases"]:
        source = directory / case["source"]
        prefix = source.with_name(source.name.removesuffix("_partial_coverage_audit.json").removesuffix("_final_audit.json"))
        if case["remaining"]:
            geometry = directory / f"{prefix.name}_{destination_geometry}.json"
            if manifests:
                screen(prefix, source_geometry, geometry, manifests)
            else:
                geometry = directory / f"{prefix.name}_{source_geometry}.json"
            evidence = list(completed_local_replays(directory,prefix.name))
            audit(prefix, table, "", geometry, evidence, auxiliary_only=True)
            final_audit = directory / f"{prefix.name}_final_audit.json"
            if final_audit.is_file():
                source = final_audit
        result = json.loads(source.read_text())
        remaining = result["remaining"]
        distance_only, replays = antipodal_replays(prefix, case["projection_orbits"])
        if isinstance(remaining, list):
            assert len(remaining) == len(set(remaining))
            used = set(remaining) & distance_only
            remaining = len(remaining)
        else:
            assert remaining == 0
            used = set()
        assert result["counts"] == case["counts"]
        assert result.get("projection_verified") or result["status"] == "FREQUENCY_BRANCH_CLOSED"
        assert result["initial_orbits"] == case["projection_orbits"]
        assert result["excluded_by_local"] + result["full_q9_verified"] + remaining == result["initial_orbits"]
        remaining -= len(used)
        assert remaining <= case["remaining"]
        cases.append(dict(case, source=source.name, remaining=remaining,
                          newly_excluded=case["remaining"] - remaining,
                          antipodal_only_indices=sorted(used), antipodal_replays=replays))
    total = sum(case["remaining"] for case in cases)
    result = dict(prior, cases=cases, remaining=total,
                  newly_excluded=prior["remaining"] - total, previous=previous.name,
                  seam_manifests=[str(path.relative_to(directory)) for path in manifests])
    with output.open("x") as file:
        json.dump(result, file, indent=2)
        file.write("\n")
    print(json.dumps(dict(remaining=total, newly_excluded=result["newly_excluded"],
                          cases=[(r["counts"], r["remaining"]) for r in cases])))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("previous", type=Path)
    parser.add_argument("table", type=Path)
    parser.add_argument("source_geometry")
    parser.add_argument("destination_geometry")
    parser.add_argument("output", type=Path)
    parser.add_argument("manifests", type=Path, nargs="*")
    args = parser.parse_args()
    run(args.previous, args.table, args.source_geometry, args.destination_geometry, args.output, args.manifests)
