"""Direct search of a retained pair, using normalized first-use coordinate histories."""
import argparse
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import json
import subprocess
from consistent_design import distance_network
from parent_family import construct
from parent_sat import PIN
from verify_distances import check_table
from triangle_cliques import find_cliques
from solve import model,save,defects


def canonical(path):
    def label(vertices):
        names={}
        return tuple(names.setdefault(a^b,len(names)) for a,b in zip(vertices,vertices[1:]))
    return min(label(path),label(path[::-1]))


def search(case,budget,certificate=False):
    parent,_=construct(case)
    seed=json.loads(subprocess.check_output(["git","show",PIN+":milestones/216-joint-word-support/data/lower-dimensional-input.json"]))["8"]["vertices"]
    groups=parent["group"];free=parent["block"]
    # At most one canonical word assignment per global cube orientation survives
    # first-use normalization; it is safe to forbid every equivalent supplied one.
    forbidden=[]
    for words in parent["nogoods"]:
        seen={}
        sequence=[]
        for a,b in zip(words,words[1:]):
            bit=(a^b).bit_length()-1
            sequence.append(seen.setdefault(bit,len(seen)))
        q=[0]
        for bit in sequence:q.append(q[-1]^(1<<bit))
        if q not in forbidden:forbidden.append(q)
    table,stats=distance_network(seed,free)
    families=find_cliques(table)
    if certificate:check_table(seed,free,table,families)
    prefix=Path(f"parent-firstproof-{case}") if certificate else None
    result=model(seed,free,budget,anchor_families=families,strengthened=True,
                 distance_table=table,certificate=prefix,nogoods=forbidden)
    if result["status"]=="SAT":
        candidate=result["vertices"]
        assert len(candidate)==99 and not defects(candidate)
        assert canonical(candidate)!=canonical(seed)
    row=dict(case=case,base=parent["base"],free=free,seed_commit=PIN,
             normalized_nogoods=forbidden,cliques=families,distance_stats=stats,
             **result)
    save(Path(f"parent-firstuse-{case}.json"),row)
    print(case,parent["base"],len(forbidden),result["status"],flush=True)
    return row


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("case",type=int)
    parser.add_argument("--budget",type=int,default=350000)
    parser.add_argument("--proof",action="store_true")
    a=parser.parse_args();search(a.case,a.budget,a.proof)
