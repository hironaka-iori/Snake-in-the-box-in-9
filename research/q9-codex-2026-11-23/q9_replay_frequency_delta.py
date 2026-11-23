"""Rebuild and check just the new certificates in a live frequency archive."""

import argparse
from contextlib import redirect_stdout
import json
from pathlib import Path

from verify_q9_dense_pair_full_lift import replay, table
from verify_q9_frequency_branch import audit, completed_replay_records, records, replay_indices


def run(prefix, layouts_path, checker, reduced_geometry=None, local_replays=(), auxiliary=(), auxiliary_only=False):
    def file(label):
        return prefix.with_name(f"{prefix.name}_{label}")

    screen_path = file("combined_geometry_screen.json")
    if not screen_path.is_file():
        screen_path = file("geometry_screen.json")
    screen = json.loads(screen_path.read_text())
    assert screen["status"]=="VERIFIED"
    allowed = set(screen["indices"])
    assert screen["initial"] == screen["excluded_by_local"]+len(allowed)
    extra_local = set()
    remaining_geometry = allowed
    if reduced_geometry:
        reduced = json.loads(reduced_geometry.read_text())
        remaining_geometry = set(reduced["indices"])
        assert reduced["status"]=="VERIFIED" and reduced["counts"]==screen["counts"]
        assert reduced["initial"]==screen["initial"] and remaining_geometry<=allowed
        assert reduced["excluded_by_local"]+len(remaining_geometry)==screen["initial"]
        extra_local.update(allowed-remaining_geometry)
    for local_replay in local_replays:
        evidence = json.loads(local_replay.read_text())
        local_excluded = set(evidence["excluded"])
        local_survivors = set(evidence["indices"])
        assert evidence["status"]=="VERIFIED_GEOMETRIC" and evidence["counts"]==screen["counts"]
        assert not local_excluded&local_survivors
        assert evidence["base"]==len(local_excluded|local_survivors)
        assert local_excluded|local_survivors<=allowed
        extra_local.update(local_excluded)
    logs = []
    sources = {}
    known = set()
    for path in sorted(prefix.parent.glob(prefix.name+"_*replay.log")):
        rows = completed_replay_records(path, "REPLAY_DONE")
        if not rows:
            continue
        added = replay_indices(rows, allowed)
        known.update(added)
        logs.append(path)
        sources[path.name] = len(added)

    newly_replayed = set()
    stem = file("saturated_full_lift")
    searches = list(auxiliary) if auxiliary_only else [(stem,layouts_path),*auxiliary]
    if not searches and not (reduced_geometry or local_replays):
        raise ValueError("No new geometry evidence or search archives to audit")
    for search,layouts in searches:
        lines = search.with_suffix(".log").read_text().splitlines(keepends=True)
        completed = [
            row for row in (json.loads(line) for line in lines if line.endswith("\n"))
            if row["status"]!="STARTED"
        ]
        finished = {row["index"] for row in completed if row["status"]=="UNSAT_DRAT_VERIFIED"}
        assert finished<=allowed
        missing_replays = finished-known-extra_local
        if not missing_replays:
            continue
        label = "" if search==stem else search.name.removeprefix(prefix.name+"_")+"_"
        target = file(f"{label}prefix_{len(completed)}_replay.log")
        profiles = json.loads(file("profiles.json").read_text())["representatives"]
        with target.open("x") as output, redirect_stdout(output):
            replay(search.with_suffix(".jsonl.gz"),profiles,table(layouts),
                   checker,False,missing_replays,len(completed))
        added = replay_indices(records(target), allowed)
        assert added==missing_replays
        known.update(added)
        newly_replayed.update(added)
        logs.append(target)
        sources[target.name] = len(added)

    projection = file("projection_replay.log")
    report = records(projection) if projection.is_file() else []
    if not report or report[-1]["status"]!="VERIFIED":
        alternative = file("integer_projection_cover.log")
        if alternative.is_file():
            independent = records(alternative)
            if independent and independent[-1]["status"]=="VERIFIED":
                projection, report = alternative, independent
    covered = bool(report and report[-1]["status"]=="VERIFIED")
    if covered:
        assert report[-1]["orbits"]==screen["initial"]
    remaining = allowed-known-extra_local
    assert (screen["excluded_by_local"]+len(extra_local)+len(known-extra_local)+len(remaining)
            == screen["initial"])
    if not remaining and covered:
        result = audit(screen,projection,logs,extra_local)
        output = file("final_audit.json")
    else:
        result = dict(status="PARTIAL_COVERAGE_VERIFIED",counts=screen["counts"],
                      projection_verified=covered,initial_orbits=screen["initial"],
                      excluded_by_local=screen["excluded_by_local"]+len(extra_local),full_q9_verified=len(known-extra_local),
                      independently_replayed=len(known),additional_local_verified=len(extra_local),
                      verified_indices=sorted(known-extra_local),remaining=sorted(remaining),sources=sources)
        output = file("partial_coverage_audit.json")
    if reduced_geometry or local_replays:
        result["local_evidence"] = (
            ([reduced_geometry.name] if reduced_geometry else [])
            + [path.name for path in local_replays]
        )
    pending = output.with_suffix(".tmp")
    pending.write_text(json.dumps(result)+"\n")
    pending.replace(output)
    print(json.dumps(dict(status=result["status"],counts=screen["counts"],
                          newly_verified=len(newly_replayed),verified=len(known-extra_local),additional_local=len(extra_local),
                          remaining=len(remaining),projection_verified=covered)),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("prefix",type=Path)
    parser.add_argument("table",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--reduced-geometry",type=Path)
    parser.add_argument("--local-replay",type=Path,action="append",default=[])
    parser.add_argument("--auxiliary",type=Path,nargs=2,action="append",default=[],
                        metavar=("SEARCH_STEM","INTERFACE_TABLE"))
    parser.add_argument("--auxiliary-only",action="store_true",
                        help="audit only explicitly listed search archives")
    args=parser.parse_args()
    if args.auxiliary_only and not (args.auxiliary or args.reduced_geometry or args.local_replay):
        parser.error("--auxiliary-only requires geometry evidence or an --auxiliary search archive")
    run(args.prefix,args.table,args.checker,args.reduced_geometry,args.local_replay,args.auxiliary,
        args.auxiliary_only)
