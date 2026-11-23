"""Check connected completion of 221-edge paths within exact Q6 interface patches."""

import argparse
from collections import defaultdict
import gzip
from itertools import islice
import json
from pathlib import Path
import re
from subprocess import CalledProcessError

from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_certify_geometric_joins import make
from q9_dense_pair_full_lift import wanted_pairs
from q9_join_interface_masks import Catalogue
from verify_q9_free_dimension_cuts import parts


def boundary_cut(component, layers, ports):
    points = set(component)
    assert 0 < len(points) == len(component) < 222
    assert all(0 <= u < 512 and u >> 6 in layers for u in points)
    boundary = {v for u in points for axis in range(9)
                if (v := u ^ (1 << axis)) >> 6 in layers and v not in points}
    # Every proper subset of the 222 path vertices must have a crossing.
    return ([-u-1 for u in sorted(points)] + [v+1 for v in sorted(boundary)]
            + [port for u in sorted(points) for port in ports[u]])


def formulate(profile, layers, catalogue, limit, shared_exterior, exterior_degree):
    ports = defaultdict(list)
    formula, size = make(profile, layers, catalogue, limit, completion_ports=True,
                         exterior_ports=ports, shared_exterior=shared_exterior, exterior_degree=exterior_degree)
    return formula, size, ports


def certify(profile, layers, catalogue, limit, budget, checker, shared_exterior, exterior_degree):
    try:
        formula, size, ports = formulate(profile, layers, catalogue, limit, shared_exterior, exterior_degree)
    except TimeoutError:
        return dict(status="DOMAIN_LIMIT")
    cuts = []
    with Cadical195(bootstrap_with=formula, with_proof=True) as solver:
        while (left := budget-solver.accum_stats()["conflicts"]) > 0:
            solver.conf_budget(left)
            answer = solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof = "\n".join(solver.get_proof() or ["0"])+"\n"
                check(formula, proof, checker)
                return dict(status="UNSAT_DRAT_VERIFIED", layouts=size, cuts=cuts, proof=proof)
            model = set(solver.get_model())
            selected = {u-1 for u in model if 0 < u <= 512 and (u-1) >> 6 in layers}
            closed = [sorted(c) for c in parts(selected,9)
                      if len(c)<222 and not any(p in model for u in c for p in ports[u])]
            if not closed:
                return dict(status="OPEN_PATCH", layouts=size, cuts=len(cuts))
            for component in closed:
                clause = boundary_cut(component, layers, ports)
                assert not any(lit in model for lit in clause)
                formula.append(clause)
                solver.add_clause(clause)
                cuts.append(component)
    return dict(status="UNKNOWN", layouts=size, cuts=len(cuts))


INDEX_PREFIX = re.compile(r'^\{\s*"index"\s*:\s*(\d+)\s*,')


def run(args):
    profiles = json.loads(args.profiles.read_text())["representatives"]
    selection = json.loads(args.selection.read_text())
    indices = set(selection["indices"])
    seen = set()
    if args.replay:
        targets = indices
        if args.only_pending:
            audit = json.loads(args.only_pending.read_text())
            assert audit["status"] == "PARTIAL_COVERAGE_VERIFIED"
            assert audit["counts"] == selection["counts"]
            targets = indices & set(audit["remaining"])
        catalogue = Catalogue(args.table,wanted=wanted_pairs(profiles,targets))
        excluded = set()
        checker_failures = []
        with gzip.open(args.archive,"rt") as archive:
            records = archive if args.prefix_records is None else islice(archive,args.start_record,args.prefix_records)
            for line in records:
                match = INDEX_PREFIX.match(line) if args.only_pending else None
                if match and int(match.group(1)) not in targets:
                    i = int(match.group(1))
                    assert i in indices and i not in seen
                    seen.add(i)
                    continue
                row = json.loads(line)
                i = row["index"]
                assert i in indices and i not in seen
                seen.add(i)
                if i not in targets or row["status"] != "UNSAT_DRAT_VERIFIED":
                    continue
                layers = set(row["layers"])
                formula, size, ports = formulate(profiles[i], layers, catalogue, args.limit,
                                                  row.get('shared_exterior',False), row.get('exterior_degree',False))
                assert size == row["layouts"]
                for cut in row["cuts"]:
                    formula.append(boundary_cut(cut, layers, ports))
                try:
                    check(formula, row["proof"], args.checker)
                except CalledProcessError as error:
                    if not args.continue_on_checker_failure:
                        raise
                    checker_failures.append(i)
                    print(json.dumps(dict(status="CHECKER_FAILED",index=i,returncode=error.returncode)),
                          flush=True)
                    continue
                excluded.add(i)
        checked = len(seen & targets)
        pending = dict(status="VERIFIED_GEOMETRIC", counts=selection["counts"],
                       base=len(targets), checked=checked, excluded=sorted(excluded),
                       indices=sorted(targets-excluded))
        if args.only_pending:
            pending["archive_records_read"] = len(seen)
            pending["filter_audit"] = str(args.only_pending)
        if args.prefix_records is not None:
            assert len(seen)==args.prefix_records-args.start_record
            pending["archive_prefix"] = args.prefix_records
            pending["archive_start"] = args.start_record
        if checker_failures:
            pending["checker_failures"] = checker_failures
        with args.replay.open("x") as out:
            out.write(json.dumps(pending)+"\n")
        print(json.dumps(dict(status=pending["status"], checked=checked, excluded=len(excluded),
                              checker_failures=len(checker_failures))))
        return
    catalogue = Catalogue(args.table,wanted=wanted_pairs(profiles,indices))
    with args.join.open() as source, gzip.open(args.archive, "xt") as archive:
        for line in source:
            row = json.loads(line)
            i = row["index"]
            if i not in indices:
                continue
            assert i not in seen
            seen.add(i)
            layers = set(row.get("layers", ()))
            if not layers and row.get("components"):
                layers = set(max(row["components"],key=lambda item:len(item["layers"]))["layers"])
            if not layers:
                continue
            try:
                outcome = certify(profiles[i],layers,catalogue,args.limit,args.budget,args.checker,
                                  args.shared_exterior,args.exterior_degree)
            except CalledProcessError as error:
                if not args.continue_on_checker_failure:
                    raise
                outcome = dict(status="CHECKER_FAILED",returncode=error.returncode)
            result = dict(index=i,layers=sorted(layers),completion_ports=True,
                          shared_exterior=args.shared_exterior,exterior_degree=args.exterior_degree,
                          **outcome)
            archive.write(json.dumps(result)+"\n")
            archive.flush()
            summary = {k:v for k,v in result.items() if k not in ("proof","cuts")}
            summary["cuts"] = len(result["cuts"]) if isinstance(result.get("cuts"),list) else result.get("cuts",0)
            print(json.dumps(summary),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles","selection","join","table","archive"):
        parser.add_argument(name,type=Path)
    parser.add_argument("checker")
    parser.add_argument("--limit",type=int,default=8000)
    parser.add_argument("--budget",type=int,default=45000)
    parser.add_argument("--shared-exterior",action="store_true")
    parser.add_argument("--exterior-degree",action="store_true")
    parser.add_argument("--replay",type=Path)
    parser.add_argument("--prefix-records",type=int)
    parser.add_argument("--start-record",type=int,default=0)
    parser.add_argument("--continue-on-checker-failure",action="store_true")
    parser.add_argument("--only-pending",type=Path)
    args = parser.parse_args()
    if args.only_pending and not args.replay:
        parser.error("--only-pending requires --replay")
    if args.prefix_records is not None and (args.prefix_records<=0 or not args.replay):
        parser.error("--prefix-records requires a positive count and --replay")
    if args.start_record<0 or args.start_record and (args.prefix_records is None or args.start_record>=args.prefix_records):
        parser.error("--start-record must be nonnegative and less than --prefix-records")
    run(args)
