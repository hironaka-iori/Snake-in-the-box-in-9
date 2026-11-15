"""A 117-vertex eight-cube forest with at most 13 components is necessary for 233 edges in Q9."""
import argparse
import json
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from solve import save


def components(selected, dimension):
    graph={v:{v^(1<<j) for j in range(dimension)} & selected for v in selected}
    assert all(len(ns)<=2 for ns in graph.values())
    parts=[]
    rest=set(selected)
    while rest:
        v=rest.pop();todo=[v];part={v}
        while todo:
            fresh=graph[todo.pop()]&rest;rest-=fresh;part|=fresh;todo.extend(fresh)
        edges=sum(len(graph[x]) for x in part)//2
        assert edges in (len(part)-1,len(part))
        parts.append((edges,sorted(part)))
    return parts


def facet_formula(fixed,size,limit,deficits):
    # Vertices of the opposite seven-face are the only undetermined sites.
    fixed=set(fixed)
    old=components(fixed,7)
    assert all(e==len(c)-1 for e,c in old)
    initial_edges=sum(e for e,_ in old)
    neighbours={v:{v^(1<<j) for j in range(7)} for v in range(128)}
    allowed=sorted(v for v in range(128) if v not in fixed or len(neighbours[v]&fixed)<2)
    pool=IDPool();select={v:pool.id(("v",v)) for v in allowed};clauses=[]
    take=size-len(fixed)
    def equal(ls,k):
        if k<0 or k>len(ls):clauses.append([]);return
        clauses.extend(CardEnc.equals(ls,bound=k,vpool=pool,encoding=EncType.totalizer).clauses)
    equal(list(select.values()),take)
    edge_flags=[];shortfall=[];static=0
    for v in allowed:
        adj=[w for w in sorted(neighbours[v]) if w in select]
        for group in combinations(adj,2 if v in fixed else 3):
            clauses.append([-select[v],*[-select[w] for w in group]])
        if deficits:
            ns=[select[w] for w in adj]
            missing=pool.id(("degree_one",v));shortfall.append(missing)
            clauses.append([-missing,select[v]])
            if v in fixed:
                clauses.append([-select[v],missing,*ns]);shortfall.append(-select[v])
            else:
                isolated=pool.id(("isolated",v));shortfall.append(isolated)
                clauses.extend([[-isolated,missing],[-select[v],isolated,*ns]])
                for j in range(len(ns)):clauses.append([-select[v],missing,*ns[:j],*ns[j+1:]])
        else:
            for w in adj:
                if w<=v:continue
                flag=pool.id(("edge",v,w));edge_flags.append(flag)
                clauses.extend([[-flag,select[v]],[-flag,select[w]],[-select[v],-select[w],flag]])
            if v in fixed:edge_flags.append(select[v])
    needed=size-limit-initial_edges
    if deficits:
        bound=2*limit-2*len(old)+len(fixed&set(allowed))
        if bound<0:clauses.append([])
        elif bound<len(shortfall):
            clauses.extend(CardEnc.atmost(shortfall,bound=bound,vpool=pool,encoding=EncType.totalizer).clauses)
        for v in allowed:
            for j,k in combinations(range(7),2):
                square=[v,v^(1<<j),v^(1<<k),v^(1<<j)^(1<<k)]
                if v==min(square) and all(x in select for x in square):
                    clauses.append([-select[x] for x in square]);static+=1
        for e,part in old:
            if not e:continue
            pset=set(part)
            x,y=[v for v in part if len(neighbours[v]&pset)==1]
            def connect(path):
                nonlocal static
                v=path[-1]
                if v==y:
                    clauses.append([-select[z] for z in path]);static+=1;return
                if len(path)+(v^y).bit_count()>8:return
                for w in sorted(neighbours[v]):
                    if w in select and w not in path and not (neighbours[w]&set(path[:-1])):
                        connect(path+[w])
            connect([x])
    elif needed>len(edge_flags):clauses.append([])
    elif needed>0:clauses.extend(CardEnc.atleast(edge_flags,bound=needed,vpool=pool,encoding=EncType.totalizer).clauses)
    return clauses, allowed, select, static


def facet_completion(fixed,size,limit,budget,tag,checker=None,deficits=False):
    fixed=set(fixed)
    clauses,allowed,select,static=facet_formula(fixed,size,limit,deficits)
    cuts=[];witness=None;status="OPEN"
    with Solver(name="cadical195",bootstrap_with=clauses,with_proof=checker is not None) as sat:
        while (remain:=budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(remain);ans=sat.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            positive=set(sat.get_model());vertices=fixed|{v|128 for v in allowed if select[v] in positive}
            parts=components(vertices,8)
            assert len(vertices)==size and sum(e for e,c in parts)>=size-limit
            cycles=[c for e,c in parts if e==len(c)]
            if not cycles:
                assert len(parts)<=limit
                witness=sorted(vertices);status="FOUND";break
            for cycle in cycles:
                upper=[v^128 for v in cycle if v>=128];assert upper
                cut=[-select[v] for v in upper];clauses.append(cut);sat.add_clause(cut);cuts.append(cycle)
        row=dict(fixed=sorted(fixed),size=size,component_limit=limit,status=status,
                 conflicts=sat.accum_stats()["conflicts"],cycles=cuts,witness=witness)
        if deficits:row["deficit_encoding"]=True;row["static_cycles"]=static
        if checker and status=="UNSAT":
            from export_drat import checked_export
            row.update(checked_export(sat,clauses,Path(tag+"-proof"),checker))
    save(Path(tag+".json"),row);print(tag,status,row["conflicts"],len(cuts),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--size",type=int,default=117);p.add_argument("--limit",type=int,default=13)
    p.add_argument("--budget",type=int,default=500000);p.add_argument("--checker",type=Path)
    a=p.parse_args();inputs=json.loads(Path("face-component-bound.json").read_bytes())["witnesses"]
    for n in range(a.start,a.stop):
        tag=f"dense8-{n}-{a.size}-{a.limit}-{a.budget}"+("-checked" if a.checker else "")
        facet_completion(inputs[str(n)],a.size,a.limit,a.budget,tag,a.checker.resolve() if a.checker else None)
