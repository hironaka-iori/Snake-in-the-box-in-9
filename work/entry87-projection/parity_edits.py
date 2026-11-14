"""Release the chronological order completely and change at most one parity vertex."""
import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
import networkx as nx
from parity_skeleton import complete,structure
from solve import paths,save,defects


def force(anchors,endcaps):
    vertices,adj,support,tips=structure(anchors)
    graph=nx.Graph(adj)
    if not nx.is_connected(graph):
        return "disconnected",sorted(min(nx.connected_components(graph),key=len))
    possible=set(tips) if endcaps else set(vertices)
    leaves={v for v in vertices if graph.degree(v)==1}
    if len(leaves)>2 or not leaves<=possible:
        return "endpoint degrees",sorted(leaves)
    # A dummy vertex turns the endpoint problem into a Hamilton cycle. When
    # two original leaves are known, they already use both endpoint slots.
    if len(leaves)==2:
        possible=leaves
    graph.add_edges_from((-1,x) for x in sorted(possible))
    must=nx.Graph()
    must.add_nodes_from(graph)
    while True:
        before=graph.number_of_edges(),must.number_of_edges()
        for x in graph:
            if graph.degree(x)<2 or must.degree(x)>2:
                return "degree contradiction",[x,graph.degree(x),must.degree(x)]
            if graph.degree(x)==2:
                must.add_edges_from(list(graph.edges(x)))
            if must.degree(x)==2:
                graph.remove_edges_from([e for e in graph.edges(x) if not must.has_edge(*e)])
        small=next((c for c in nx.cycle_basis(must) if len(c)<len(graph)),None)
        if small:
            return "forced proper cycle",small
        if (graph.number_of_edges(),must.number_of_edges())==before:
            return None,None


def examine(p,start,end):
    q=paths()[1]
    base=sorted(q[p::2])
    m=len(base)
    assert m==(96 if p else 97)
    outside=[v for v in range(512) if v.bit_count()%2==p and v not in base]
    count=Counter();calls=0;examples={}
    row=dict(parity=p,first=start,last=min(end,m),outside=len(outside))
    for i in range(start,min(end,m)):
        for w in outside:
            trial=base.copy();trial[i]=w
            status,detail=force(trial,p==1)
            if status is None:
                calls+=1
                result=complete(trial,p==1)
                if result["status"]=="FOUND":
                    path=result["vertices"]
                    assert len(path)==193 and not defects(path)
                    row.update(witness=path,removed=base[i],added=w)
                    print("WITNESS",p,base[i],w,flush=True)
                    save(Path(f"parity-edit-{p}-{start}-{end}.json"),row)
                    return
                status=result["reason"]
            count[status]+=1
            if status not in examples:
                examples[status]=[base[i],w,detail]
    assert sum(count.values())==(min(end,m)-start)*len(outside)
    row.update(counts=count,solver_calls=calls,examples=examples)
    save(Path(f"parity-edit-{p}-{start}-{end}.json"),row)
    print(p,start,end,row["counts"],calls,flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("parity",type=int,choices=(0,1))
    parser.add_argument("start",type=int)
    parser.add_argument("end",type=int)
    args=parser.parse_args()
    examine(args.parity,args.start,args.end)
