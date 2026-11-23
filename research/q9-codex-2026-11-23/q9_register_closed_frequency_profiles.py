"""Register only fully covered 221-edge direction triples."""

import argparse
import json
from pathlib import Path

from q9_221_use_verified_profiles import triple_floor
from q9_audit_mixed_endpoint_cover import cover


def register(previous, destination, incoming):
    directory = previous.parent
    ledger = set(map(tuple, json.loads(previous.read_text())))
    counts = {}
    for label in incoming:
        prefix = directory / f"q9_pair_{label}"
        final_audit = prefix.with_name(prefix.name+"_final_audit.json")
        if final_audit.is_file():
            audit = json.loads(final_audit.read_text())
            assert audit["status"] == "FREQUENCY_BRANCH_CLOSED" and audit["remaining"] == 0
        else:
            baseline = prefix.with_name(prefix.name+"_partial_coverage_audit.json")
            audit = cover(baseline)
            assert audit["status"] == "MIXED_ENDPOINT_BRANCH_CLOSED" and not audit["remaining"]
        source = prefix.with_name(prefix.name+"_integer_projection_cover.log")
        records = [json.loads(line) for line in source.read_text().splitlines()]
        triple = tuple(map(int,label.split("_")))
        assert tuple(audit["counts"])==triple==tuple(records[-1]["counts"])
        assert records[0]["status"]=="MARGIN_COVER_VERIFIED" and records[-1]["status"]=="VERIFIED"
        assert records[-1]["orbits"]==audit["initial_orbits"]
        assert audit["initial_orbits"]==audit["excluded_by_local"]+audit["full_q9_verified"]
        assert triple not in ledger
        ledger.add(triple)
        counts[label]=audit["initial_orbits"]
    with destination.open("x") as output:
        json.dump(sorted(ledger),output)
        output.write("\n")
    print(json.dumps(dict(status="VERIFIED",excluded_profiles=len(ledger),
                          new_profiles=counts,new_orbits=sum(counts.values()),
                          floors=[triple_floor(ledger,k) for k in range(4)])),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("previous",type=Path)
    parser.add_argument("destination",type=Path)
    parser.add_argument("labels",nargs="+")
    args=parser.parse_args()
    register(args.previous,args.destination,args.labels)
