"""Select connected projected layers covered by complete interface catalogues."""

import argparse
from itertools import combinations
import json
from pathlib import Path

from q9_certify_geometric_joins import domain_graph
from q9_dense_pair_full_lift import wanted_pairs
from q9_join_interface_masks import Catalogue
from q9_three_tight_pairs import BONDS


def patch_neighbors(row,banks):
    edges,components,crossings = row
    neighbors = [{} for _ in edges]
    for (a,b),r in zip(BONDS,crossings):
        ab = (edges[a],components[a],edges[b],components[b],r)
        if ab in banks:
            neighbors[a][b] = ab
            neighbors[b][a] = (*ab[2:4],*ab[:2],r)
    return neighbors


def pick(row,banks):
    neighbors=patch_neighbors(row,banks)
    visited = set()
    patches = []
    for root, adjacent in enumerate(neighbors):
        if root in visited or not adjacent:
            continue
        found = {root}
        stack = [root]
        while stack:
            a = stack.pop()
            new = set(neighbors[a])-found
            found.update(new)
            stack.extend(new)
        visited.update(found)
        distinct_roots = min(len(set.intersection(*(set(banks[k]) for k in neighbors[a].values())))
                             for a in found)
        bonds = sum(len(neighbors[a]) for a in found)//2
        patches.append((-len(found),distinct_roots,-bonds,sorted(found)))
    return min(patches) if patches else None


def pick_with_limit(row,catalogue,limit):
    neighbors=patch_neighbors(row,catalogue.banks)
    occupied=tuple(a for a,adjacent in enumerate(neighbors) if adjacent)
    for n in range(len(occupied),1,-1):
        choices=[]
        for layers in combinations(occupied,n):
            allowed=set(layers)
            reached={layers[0]}
            pending=[layers[0]]
            while pending:
                new=(set(neighbors[pending.pop()])&allowed)-reached
                reached.update(new)
                pending.extend(new)
            if reached!=allowed:
                continue
            try:
                domains=domain_graph(row,allowed,catalogue,limit)
            except TimeoutError:
                continue
            choices.append((-n,sum(map(len,domains.values())),0,list(layers)))
        if choices:
            return min(choices)
    return None


def run(args):
    profiles = json.loads(args.profiles.read_text())["representatives"]
    source = json.loads(args.screen.read_text())
    audit = json.loads(args.audit.read_text()) if args.audit else None
    if audit:
        assert audit["status"] == "PARTIAL_COVERAGE_VERIFIED" and audit["counts"] == source["counts"]
        indices = set(source["indices"]) & set(audit["remaining"])
    else:
        indices = set(source["indices"])
    assert source["status"] == "VERIFIED"
    for path in args.skip_selection:
        skip = json.loads(path.read_text())
        assert skip["counts"] == source["counts"]
        indices.difference_update(skip["indices"])
    if args.retry_log:
        pending=set()
        proven=set()
        for path in args.retry_log:
            with path.open() as log:
                for row in (json.loads(line) for line in log if line.endswith("\n")):
                    if row["status"] in ("DOMAIN_LIMIT","UNKNOWN","OPEN_PATCH","CHECKER_FAILED"):
                        pending.add(row["index"])
                    elif row["status"]=="UNSAT_DRAT_VERIFIED":
                        proven.add(row["index"])
        indices &= pending-proven
    catalogue=Catalogue(args.table,wanted=wanted_pairs(profiles,indices))
    options = []
    for index in sorted(indices):
        if args.domain_limit is None:
            best = pick(profiles[index],catalogue.banks)
        else:
            best = pick_with_limit(profiles[index],catalogue,args.domain_limit)
        if best is not None:
            options.append((*best,index))
    options.sort()
    chosen = options[:args.limit]
    with args.selection.open("x") as out:
        out.write(json.dumps(dict(counts=source["counts"],indices=[row[-1] for row in chosen]))+"\n")
    with args.patches.open("x") as out:
        for _,_,_,layers,index in chosen:
            out.write(json.dumps(dict(index=index,layers=layers))+"\n")
    pinned = sum(roots==0 for _,roots,*_ in chosen)
    print(json.dumps(dict(counts=source["counts"],eligible=len(options),selected=len(chosen),
                          incompatible_root_domains=pinned)),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    for name in ("profiles","screen","table","selection","patches"):
        parser.add_argument(name,type=Path)
    parser.add_argument("--audit",type=Path)
    parser.add_argument("--skip-selection",type=Path,action="append",default=[])
    parser.add_argument("--limit",type=int,default=400)
    parser.add_argument("--domain-limit",type=int)
    parser.add_argument("--retry-log",action="append",default=[],type=Path)
    args=parser.parse_args()
    if args.limit<=0 or args.domain_limit is not None and args.domain_limit<=0:
        parser.error("limits must be positive")
    run(args)
