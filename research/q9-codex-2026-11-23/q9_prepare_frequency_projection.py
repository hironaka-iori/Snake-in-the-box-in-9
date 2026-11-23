"""Generate and independently verify projection coverage before local screening."""

import argparse
import json
from pathlib import Path

from q9_extend_geometry_screen import canonical_patterns, compile_patterns, screen
from q9_three_tight_pairs import canonical, projections
from verify_q9_projection_margin_cover import audit


def write(path, row):
    with path.open("x") as output:
        output.write(json.dumps(row) + "\n")


def run(counts, prefix, library):
    def file(label, extension="json"):
        return prefix.with_name(f"{prefix.name}_{label}.{extension}")

    labelled = set(projections(counts))
    rows = sorted({canonical(row, counts) for row in labelled})
    original = dict(labelled=len(labelled), orbits=len(rows), representatives=rows)
    write(file("profiles"), original)
    print(json.dumps(dict(status="GENERATED", counts=counts, orbits=len(rows))), flush=True)

    coverage = audit(counts, original)
    all_indices = list(range(len(rows)))
    base = dict(status="VERIFIED", counts=counts, initial=len(rows),
                excluded_by_local=0, indices=all_indices)
    with file("integer_projection_cover", "log").open("x") as log:
        log.write(json.dumps(coverage) + "\n")
        log.write(json.dumps(dict(status="VERIFIED", counts=counts,
                                  orbits=coverage["orbits"], starting_orbits=coverage["orbits"],
                                  excluded=0, unresolved=[])) + "\n")
    write(file("geometry_screen"), base)

    keep, drop = screen(rows, all_indices, compile_patterns(canonical_patterns(library)))
    assert len(keep) + len(drop) == len(rows)
    write(file("geometry_after_latest_replays"), dict(
        base, indices=keep, new_exclusions=drop, excluded_by_local=len(drop),
        certificate_library=str(library)))
    print(json.dumps(dict(status="VERIFIED", counts=counts, orbits=len(rows),
                          local_exclusions=len(drop), remaining=len(keep))), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("counts", type=int, nargs=3)
    parser.add_argument("prefix", type=Path)
    parser.add_argument("library", type=Path)
    args = parser.parse_args()
    run(tuple(args.counts), args.prefix, args.library)
