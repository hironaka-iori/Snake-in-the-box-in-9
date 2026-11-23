"""Lift a connected family of exact Q6 layout domains into a full Q9 SAT instance."""

import argparse
import gzip
import json
from pathlib import Path

from pysat.formula import IDPool

from q9_certify_geometric_joins import domain_graph, pin_domains, prune_interface_domains
from q9_dense_pair_full_lift import sibling_cases, wanted_pairs
from q9_join_interface_masks import Catalogue
from q9_three_tight_anchored_lift import candidate, form, verify


def run(args):
    profiles = json.loads(args.profiles.read_text())["representatives"]
    indices = set(json.loads(args.selection.read_text())["indices"])
    catalogue = Catalogue(args.table, wanted=wanted_pairs(profiles, indices))
    with gzip.open(args.archive,"xt") as output:
        for line in args.joins.read_text().splitlines():
            rec = json.loads(line)
            i = rec["index"]
            if i not in indices or any(i in sibling_cases(path) for path in args.skip_log):
                continue
            layers = set(rec.get("layers",()))
            if not layers and rec.get("components"):
                layers = set(max(rec["components"],key=lambda item:len(item["layers"]))["layers"])
            if len(layers)<2:
                continue
            row = profiles[i]
            started = dict(index=i,layers=sorted(layers),key=[],domain_limit=args.limit,
                           saturated=True,balanced=args.balanced)
            layer_colour_balance = args.antipodal or args.distance_three
            if layer_colour_balance:
                started["layer_colour_balance"] = True
            if args.antipodal:
                started["antipodal"] = True
            if args.distance_three:
                started["distance_three"] = True
            try:
                domains = domain_graph(row,layers,catalogue,args.limit)
            except TimeoutError:
                result = dict(**started,status="DOMAIN_LIMIT",layout_count=0)
                output.write(json.dumps(result)+"\n")
                output.flush()
                print(json.dumps(result),flush=True)
                continue
            if args.arc_consistency:
                started["arc_consistency"] = True
                prune_interface_domains(row, catalogue, domains)
            layout_count = sum(map(len,domains.values()))
            print(json.dumps(dict(**started,status="STARTED",layout_count=layout_count)),flush=True)
            f = form(row, True, args.balanced, layer_colour_balance,
                     antipodal=args.antipodal, distance_three=args.distance_three)
            pin_domains(f,IDPool(start_from=f.nv+1),domains)
            extra = f.nv+1
            f.append([extra])
            status,cycles,points,proposed = candidate(f,[extra],args.budget,True)
            proof = verify(f,[extra],cycles,args.checker,proposed) if status=="UNSAT" else None
            status = "UNSAT_DRAT_VERIFIED" if proof else status
            result = dict(**started,status=status,layout_count=layout_count)
            output.write(json.dumps(dict(**result,cycles=cycles,proof=proof,points=points))+"\n")
            output.flush()
            print(json.dumps(dict(**result,cycles=len(cycles))),flush=True)
            if points:
                break


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles","selection","joins","table","archive"):
        parser.add_argument(name,type=Path)
    parser.add_argument("checker")
    parser.add_argument("--budget",type=int,default=200000)
    parser.add_argument("--limit",type=int,default=9000)
    parser.add_argument("--balanced",action="store_true")
    endpoint_scope = parser.add_mutually_exclusive_group()
    endpoint_scope.add_argument("--antipodal", action="store_true")
    endpoint_scope.add_argument("--distance-three", action="store_true")
    parser.add_argument("--arc-consistency",action="store_true")
    parser.add_argument("--skip-log",type=Path,action="append",default=[])
    args = parser.parse_args()
    if (args.antipodal or args.distance_three) and not args.balanced:
        parser.error("an endpoint-distance constraint requires --balanced")
    run(args)
