"""Audit binary cube coverage and each certified leaf against a rebuilt formula."""

import argparse
import json
from pathlib import Path
import subprocess

from pysat.formula import CNF

from q9_221_compact_selector import build_compact
from q9_global_lookahead import leaves
from verify_q9_free_dimension_cuts import deg, parts


def verify(stem,distance,ledger,checker):
    tree = json.loads(stem.with_suffix(".tree.json").read_text())
    cubes = list(leaves(tree))
    formula,end = build_compact(221,distance,json.loads(ledger.read_text()))
    log = [json.loads(line) for line in stem.with_suffix(".jsonl").read_text().splitlines()]
    assert log[0]["status"]=="LOOKAHEAD_COVER_STARTED"
    assert log[0]["distance"]==distance and log[0]["leaves"]==len(cubes)
    assert log[0]["clauses"]==len(formula.clauses)
    unit_set={line[0] for line in formula.clauses if len(line)==1}
    ids=set()
    trivial=0
    for row in log:
        if row["status"]!="UNSAT_DRAT_VERIFIED":
            continue
        index=row["index"]
        assert 0<=index<len(cubes) and index not in ids
        name=stem.with_name(f"{stem.name}_leaf{index:03d}")
        cnf=name.with_suffix(".cnf")
        archived=CNF(from_file=str(cnf))
        expected_units=cubes[index]["assumptions"] or [end+1]
        prefix=len(formula.clauses)
        assert archived.clauses[:prefix]==formula.clauses
        assert archived.clauses[-len(expected_units):]==[[x] for x in expected_units]
        for clause in archived.clauses[prefix:-len(expected_units)]:
            assert clause and all(-512<=x<=-1 for x in clause)
            cycle={-x-1 for x in clause}
            assert len(cycle)==len(clause) and len(parts(cycle,9))==1
            assert all(deg(cycle,v,9)==2 for v in cycle)
        proof=name.with_suffix(".drat")
        status=subprocess.run([checker,str(cnf),str(proof)],capture_output=True,check=True)
        assert b"s VERIFIED" in status.stdout
        ids.add(index)
        trivial+=any(-x in unit_set for x in expected_units)
    remaining=sorted(set(range(len(cubes)))-ids)
    return dict(status="ENDPOINT_COVER_VERIFIED" if not remaining else "PARTIAL_ENDPOINT_COVER",
                distance=distance,leaves=len(cubes),verified=sorted(ids),remaining=remaining,
                contradictions_to_base_units=trivial)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("stem",type=Path)
    parser.add_argument("distance",type=int,choices=(3,5,7,9))
    parser.add_argument("ledger",type=Path)
    parser.add_argument("checker")
    args=parser.parse_args()
    print(json.dumps(verify(args.stem,args.distance,args.ledger,args.checker)))
