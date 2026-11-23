"""Prove Q9 projection exclusions with one exhaustive anchor and free neighboring faces."""

import argparse
from collections import defaultdict
import gzip
import json
from pathlib import Path

from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_certify_geometric_joins import require_completion_ports
from q9_certify_local_connectivity import boundary_cut
from q9_dense_pair_full_lift import pin_pair
from q9_geometry_cut_library import certificate_pattern
from q9_overlapping_cross18 import value_literals
from q9_square_census import add_popcount
from q9_three_tight_pairs import BONDS
from q9_three_tight_star_refine import anchor_list
from verify_q9_free_dimension_cuts import parts


def build(row, root, layers, anchors):
    edges, components, crossings = row
    selected = {64*layer+u for layer in layers for u in range(64)}
    f = CNF(from_clauses=[[512,-512]])
    pool = IDPool(start_from=513)
    internal = defaultdict(list)
    interfaces = defaultdict(list)
    for u in sorted(selected):
        for axis in range(9):
            v = u | (1<<axis)
            if v==u or v not in selected:
                continue
            bond=pool.id()
            f.extend([[-bond,u+1],[-bond,v+1],[bond,-u-1,-v-1]])
            if axis<6:
                internal[u>>6].append(bond)
            else:
                interfaces[u>>6,v>>6].append(bond)
    def count(block,total):
        f.extend([lit] for lit in value_literals(add_popcount(f,pool,[block]),total))
    for layer in sorted(layers):
        count(list(range(64*layer+1,64*layer+65)),edges[layer]+components[layer])
        count(internal[layer],edges[layer])
    for (u,v),r in zip(BONDS,crossings):
        if u in layers and v in layers:
            count(interfaces[u,v],r)
    outward=defaultdict(list)
    require_completion_ports(f,pool,row,layers,selected,exterior_ports=outward,
                             shared_exterior=True,exterior_degree=True)
    pin_pair(f,[root],[(mask,) for mask in anchors])
    return f,outward


def prove(row, root, layers, anchors, budget, checker):
    f,ports=build(row,root,layers,anchors)
    cuts=[]
    with Cadical195(bootstrap_with=f,with_proof=True) as solver:
        while (left:=budget-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(left)
            answer=solver.solve_limited()
            if answer is None:
                break
            if answer is False:
                proof="\n".join(solver.get_proof() or ["0"])+"\n"
                check(f,proof,checker)
                return dict(status="UNSAT_DRAT_VERIFIED", proof=proof, cuts=cuts)
            model=set(solver.get_model())
            selected={u-1 for u in model if 1<=u<=512 and (u-1)>>6 in layers}
            closed=[sorted(piece) for piece in parts(selected,9)
                    if len(piece)<222 and not any(lit in model for u in piece for lit in ports[u])]
            if not closed:
                return dict(status="OPEN_PATCH", cuts=len(cuts))
            for piece in closed:
                clause=boundary_cut(piece,layers,ports)
                assert all(lit not in model for lit in clause)
                f.append(clause)
                solver.add_clause(clause)
                cuts.append(piece)
        return dict(status="UNKNOWN", conflicts=solver.accum_stats()["conflicts"], cuts=len(cuts))


def choose(row, cache):
    edges,components,crossings=row
    neighbors=defaultdict(list)
    for (u,v),r in zip(BONDS,crossings):
        if r:
            neighbors[u].append(v)
            neighbors[v].append(u)
    candidates=[]
    for u,others in neighbors.items():
        kind=edges[u],components[u]
        if kind[0] not in (24,25,26):
            continue
        if kind not in cache:
            cache[kind]=anchor_list(kind[1],kind[0])
        anchors=cache[kind]
        if anchors:
            layers={u,*others}
            candidates.append((len(anchors),-len(layers),u,layers,anchors))
    return min(candidates) if candidates else None


def run(args):
    profiles=json.loads(args.profiles.read_text())["representatives"]
    picked=json.loads(args.selection.read_text())
    assert picked["status"]=="VERIFIED_PROJECTION_SELECTION"
    indices=set(picked["indices"])
    assert len(indices)==len(picked["indices"])
    if args.replay:
        verified=set()
        seen=set()
        patterns={}
        with gzip.open(args.archive,"rt") as source:
            for line in source:
                record=json.loads(line)
                i=record["index"]
                assert i in indices and i not in seen
                seen.add(i)
                if record["status"]!="UNSAT_DRAT_VERIFIED":
                    continue
                row=profiles[i]
                root=record["root"]
                layers=set(record["layers"])
                assert root in layers and len(layers)>=2
                anchors=anchor_list(row[1][root],row[0][root])
                assert len(anchors)==record["anchors"]
                f,ports=build(row,root,layers,anchors)
                f.extend(boundary_cut(piece,layers,ports) for piece in record["cuts"])
                check(f,record["proof"],args.checker)
                verified.add(i)
                if args.patterns:
                    faces,links=certificate_pattern(row,dict(layers=record["layers"],completion_ports=True))
                    patterns[faces,links]=dict(faces=faces,links=links,source=picked["counts"],index=i)
        if args.patterns:
            with args.patterns.open("x") as target:
                json.dump(dict(source_certificates=len(verified),patterns=list(patterns.values())),target)
                target.write("\n")
        print(json.dumps(dict(status="VERIFIED_GEOMETRIC",counts=picked["counts"],base=len(indices),
                              excluded=sorted(verified),indices=sorted(indices-verified))),flush=True)
        return
    cache={}
    plan=[]
    for i in sorted(indices):
        found=choose(profiles[i],cache)
        if found:
            n, size, root, layers, anchors=found
            if args.full_cube:
                layers=set(range(8))
            plan.append((n,size,i,root,layers,anchors))
    print(json.dumps(dict(status="STARTED",eligible=len(plan),
                          selected=min(args.limit,len(plan)))),flush=True)
    with gzip.open(args.archive,"xt") as output:
        for n,_,i,root,layers,anchors in sorted(plan)[:args.limit]:
            proved=prove(profiles[i],root,layers,anchors,args.budget,args.checker)
            record=dict(index=i,root=root,layers=sorted(layers),anchors=n,**proved)
            output.write(json.dumps(record)+"\n")
            output.flush()
            compact={k:v for k,v in record.items() if k!="proof"}
            if isinstance(compact["cuts"],list):
                compact["cuts"]=len(compact["cuts"])
            print(json.dumps(compact),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("profiles","selection","archive"):
        parser.add_argument(name,type=Path)
    parser.add_argument("checker")
    parser.add_argument("--budget",type=int,default=20000)
    parser.add_argument("--limit",type=int,default=48)
    parser.add_argument("--full-cube",action="store_true")
    parser.add_argument("--replay",action="store_true")
    parser.add_argument("--patterns",type=Path)
    args=parser.parse_args()
    if args.patterns and not args.replay:
        parser.error("Pattern export requires independent replay.")
    run(args)
