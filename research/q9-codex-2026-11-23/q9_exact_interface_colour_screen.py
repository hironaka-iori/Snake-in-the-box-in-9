"""Screen weighted Q3 projections with exact Q6 interface colour signatures."""

import argparse
from collections import defaultdict
from functools import lru_cache
import gzip
import json
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_star_interfaces import check
from q9_colour_three_axis import unary_exact
from q9_dense_pair_full_lift import table
from q9_three_tight_pairs import BONDS


EVEN = sum(1<<u for u in range(64) if u.bit_count()%2==0)


def colour_signatures(path):
    signatures = defaultdict(set)
    for (e,c,f,d,r),masks in table(path).items():
        for a,b in masks:
            p,q,z = ((a&EVEN).bit_count(),(b&EVEN).bit_count(),(a&b&EVEN).bit_count())
            reverse_colours = e+c-p,f+d-q,r-z
            signatures[e,c,f,d,r].update(((p,q,z),reverse_colours))
            signatures[f,d,e,c,r].update(((q,p,z),(reverse_colours[1],reverse_colours[0],r-z)))
    return signatures


@lru_cache(maxsize=1)
def dense_population_balances():
    from q9_colour_three_axis import catalogue_balances
    from q9_three_tight_star_refine import anchor_list

    balances = catalogue_balances()
    counts = {(mask & EVEN).bit_count() for mask in anchor_list(4,24)}
    assert counts
    balances[24,4] = tuple(sorted(counts | {28-n for n in counts}))
    return balances


def add_colour_problem(f, pool, row, counts, signatures, start_even=None, dense_balances=False):
    edges,parts,crossings = row
    end = sum((n%2)<<axis for axis,n in enumerate(counts))

    def unary(n):
        values = [pool.id() for _ in range(n)]
        f.extend([[-b,a] for a,b in zip(values,values[1:])])
        return values

    ports = {bond:unary(r) for bond,r in zip(BONDS,crossings)}
    black = [unary(min(32,e+c)) for e,c in zip(edges,parts)]
    for u,values in enumerate(black):
        n = edges[u]+parts[u]
        if n>32:
            f.append([values[n-33]])
        endpoint_even = 0
        endpoint_terms = []
        if start_even is None:
            endpoint_even = int(u==0)+int(u==end and end.bit_count()%2==1)
        else:
            if u==0:
                endpoint_terms.append(start_even)
            if u==end:
                endpoint_terms.append(start_even if end.bit_count()%2 else -start_even)
        duplicate = [pool.id() for _ in values]
        for a,b in zip(values,duplicate):
            f.extend([[-a,b],[a,-b]])
        incident = [p for bond,bank in ports.items() if u in bond for p in bank]
        target = 2*len(values)-edges[u]-endpoint_even
        f.extend(CardEnc.equals(incident+endpoint_terms+[-p for p in values+duplicate],target,
                                vpool=pool,encoding=EncType.seqcounter))
    if dense_balances:
        populations = dense_population_balances()
        for u,values in enumerate(black):
            allowed = populations.get((edges[u],parts[u]))
            if allowed is not None:
                selectors = []
                for value in allowed:
                    selector = pool.id()
                    selectors.append(selector)
                    f.extend([-selector,literal] for literal in unary_exact(values,value))
                f.append(selectors)
    for (u,v),r in zip(BONDS,crossings):
        options = signatures.get((edges[u],parts[u],edges[v],parts[v],r))
        if not options:
            continue
        choices = []
        for p,q,z in sorted(options):
            item = pool.id()
            choices.append(item)
            literals = unary_exact(black[u],p)+unary_exact(black[v],q)+unary_exact(ports[u,v],z)
            f.extend([[-item,t] for t in literals])
        f.append(choices)
    return black,ports


def colour_problem(row, counts, signatures, dense_balances=False):
    f = CNF()
    add_colour_problem(f,IDPool(),row,counts,signatures,dense_balances=dense_balances)
    return f


def run(profiles, selection, interface_path, archive, checker, replay=False, dense_balances=False):
    source = json.loads(profiles.read_text())["representatives"]
    picked = json.loads(selection.read_text())
    counts = picked["counts"]
    allowed = set(picked["indices"])
    signatures = colour_signatures(interface_path)
    checked = set()
    if replay:
        with gzip.open(archive,"rt") as proof_file:
            for row in map(json.loads,proof_file):
                i = row["index"]
                assert i in allowed and i not in checked
                check(colour_problem(source[i],counts,signatures,dense_balances),row["proof"],checker)
                checked.add(i)
        print(json.dumps(dict(status="VERIFIED_GEOMETRIC",counts=counts,base=len(allowed),
                              excluded=sorted(checked),indices=sorted(allowed-checked))),flush=True)
        return
    with gzip.open(archive,"wt") as proof_file:
        for i in sorted(allowed):
            f = colour_problem(source[i],counts,signatures,dense_balances)
            with Cadical195(bootstrap_with=f,with_proof=True) as solver:
                if solver.solve():
                    continue
                proof = "\n".join(solver.get_proof() or ["0"])+"\n"
            check(f,proof,checker)
            proof_file.write(json.dumps(dict(index=i,proof=proof))+"\n")
            proof_file.flush()
            checked.add(i)
    print(json.dumps(dict(status="COLOUR_CERTIFICATES_GENERATED",counts=counts,
                          base=len(allowed),certificates=len(checked))),flush=True)


if __name__=="__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("profiles",type=Path)
    parser.add_argument("selection",type=Path)
    parser.add_argument("interfaces",type=Path)
    parser.add_argument("archive",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--replay",action="store_true")
    parser.add_argument("--dense-balances",action="store_true")
    args = parser.parse_args()
    run(args.profiles,args.selection,args.interfaces,args.archive,args.checker,args.replay,args.dense_balances)
