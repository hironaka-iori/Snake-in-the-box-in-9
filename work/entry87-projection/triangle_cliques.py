"""Repeated triple-distance propagation and its same-parity clique certificates."""
from itertools import combinations
from pathlib import Path
from time import monotonic
import argparse
import networkx as nx
from consistent_design import distance_network
from solve import paths,model,save


def find_cliques(table):
    result=[]
    for p in (0,1):
        vertices=list(range(p,len(table),2))
        graph=nx.Graph();graph.add_nodes_from(vertices)
        graph.add_edges_from((i,j) for i,j in combinations(vertices,2) if not table[i][j]&1)
        clique,_=nx.max_weight_clique(graph,weight=None)
        assert all(not table[i][j]&1 for i,j in combinations(clique,2))
        result.append(sorted(clique))
    return result


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bits")
    ap.add_argument("--solver-budget",type=int)
    args=ap.parse_args()
    q=paths()[1]
    masks=[tuple(map(int,args.bits))] if args.bits else combinations(range(9),6)
    records=[]
    output=Path("triangle-"+(args.bits or "all")+".json")
    for bits in masks:
        table,r=distance_network(q,bits)
        cliques=find_cliques(table)
        r["cliques"]=cliques
        if max(map(len,cliques))>32:
            r["status"]="CAPACITY_EXCLUDED"
        elif args.solver_budget:
            t=monotonic()
            r["search"]=model(q,bits,args.solver_budget,anchor_families=cliques,
                              strengthened=True,distance_table=table)
            r["search_seconds"]=round(monotonic()-t,2)
        records.append(r)
        save(output,records)
        print(bits,list(map(len,cliques)),r.get("status",r.get("search",{}).get("status","")),flush=True)
