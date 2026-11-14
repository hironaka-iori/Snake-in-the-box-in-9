"""Exact free-order completion of a prescribed set of one vertex parity in Q9."""
import argparse
from itertools import combinations
from pathlib import Path
from ortools.sat.python import cp_model
from solve import defects,paths,save


def structure(anchors):
    ordered=sorted(set(anchors))
    assert len(ordered)==len(anchors) and len({v.bit_count()%2 for v in anchors})==1
    active=set(ordered)
    supports={};tips={};adj={v:set() for v in ordered}
    parity=ordered[0].bit_count()%2
    for w in range(512):
        if w.bit_count()%2==parity:continue
        neighbors=sorted(w^(1<<b) for b in range(9) if (w^(1<<b)) in active)
        if len(neighbors)==1:
            tips.setdefault(neighbors[0],[]).append(w)
        if len(neighbors)==2:
            a,b=neighbors
            adj[a].add(b);adj[b].add(a)
            supports.setdefault((a,b),[]).append(w)
    return ordered,adj,supports,tips


def complete(anchors,endcaps=False):
    vertices,adj,support,tips=structure(anchors)
    components=[];unseen=set(vertices)
    while unseen:
        root=min(unseen);stack=[root];unseen.remove(root);component=[]
        while stack:
            x=stack.pop();component.append(x)
            for y in adj[x]&unseen:
                unseen.remove(y);stack.append(y)
        components.append(sorted(component))
    leaves=[x for x in vertices if len(adj[x])==1]
    endpoints={x for x in vertices if not endcaps or x in tips}
    r=dict(size=len(vertices),endcaps=endcaps,edge_count=len(support),
           components=list(map(len,components)),leaves=leaves,endpoint_options=sorted(endpoints))
    if len(components)>1 or any(not adj[v] for v in vertices) or len(leaves)>2 or not set(leaves)<=endpoints or len(endpoints)<2:
        return dict(**r,status="EXCLUDED",reason="components or degrees")
    # One artificial vertex closes a Hamilton path to a Hamilton cycle.
    # Its admitted incident edges encode the possible endpoint anchors.
    idx={v:i+1 for i,v in enumerate(vertices)}
    model=cp_model.CpModel()
    arcs=[];links={}
    allowed=[(i,j) for (a,b) in support for i,j in ((idx[a],idx[b]),(idx[b],idx[a]))]
    allowed += [(i,j) for v in sorted(endpoints) for i,j in ((0,idx[v]),(idx[v],0))]
    for i,j in allowed:
        lit=model.new_bool_var(f"edge_{i}_{j}")
        arcs.append((i,j,lit));links[i,j]=lit
    model.add_circuit(arcs)
    solver=cp_model.CpSolver()
    solver.parameters.num_search_workers=1
    status=solver.solve(model)
    if status==cp_model.INFEASIBLE:
        return dict(**r,status="EXCLUDED",reason="Hamilton path infeasible",
                    branches=solver.num_branches,conflicts=solver.num_conflicts)
    assert status in (cp_model.OPTIMAL,cp_model.FEASIBLE)
    successor={i:j for (i,j),lit in links.items() if solver.value(lit)}
    order=[];i=successor[0]
    while i:
        order.append(vertices[i-1]);i=successor[i]
        assert len(order)<=len(vertices)
    assert set(order)==set(vertices)
    path=[order[0]]
    for a,b in zip(order,order[1:]):
        path.extend([support[tuple(sorted((a,b)))][0],b])
    if endcaps:
        path=[tips[order[0]][0],*path,tips[order[-1]][0]]
    assert not defects(path)
    return dict(**r,status="FOUND",vertices=path)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--source",action="store_true")
    args=parser.parse_args()
    q=paths()[0 if args.source else 1]
    cases=[]
    for p in range(2):
        row=complete(q[p::2],len(q[p::2])==96)
        print(p,row["status"],row.get("reason"),len(row.get("vertices",[])),flush=True)
        cases.append(row)
    save(Path("parity-skeleton-"+("source" if args.source else "target")+".json"),cases)
