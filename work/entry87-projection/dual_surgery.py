"""Select an arbitrary induced path from a source path and its alternative endpoint routes."""
import argparse,json
from collections import deque
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from export_drat import checked_export
from solve import BANK,BANK_HASH,sha256,defects,save
from syndrome import neighbour_syndrome


def domain(source,slack):
    S=set(source);Y=neighbour_syndrome(S);x=source[0];y=source[-1]
    graph={v:{v^(1<<b) for b in range(9)}&Y for v in Y}
    def levels(z):
        dist={z:0};queue=deque([z])
        while queue:
            v=queue.popleft()
            for w in graph[v]-dist.keys():dist[w]=dist[v]+1;queue.append(w)
        return dist
    a=levels(x);b=levels(y);assert a.keys()==b.keys()
    if slack==-2:extra=Y
    elif slack==-1:extra=set(a)
    else:extra={v for v in a if a[v]+b[v]<=a[y]+slack}
    return sorted(S|extra),a[y]


def examine(source,tag,slack,budget,checker=None,desired=193):
    nodes,d=domain(source,slack);possible=set(nodes);pool=IDPool()
    var={v:pool.id(("selected",v)) for v in nodes}
    end={v:pool.id(("endpoint",v)) for v in nodes}
    graph={v:sorted({v^(1<<b) for b in range(9)}&possible) for v in nodes}
    cap=Path("dual-union-proof-"+tag);output=[];dynamic=[]
    with Solver(name="cadical195",with_proof=checker is not None) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:output.append(c)
        def eq(lits,num):
            for c in CardEnc.equals(lits,bound=num,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        eq(list(var.values()),desired);eq(list(end.values()),2)
        for v,ns in graph.items():
            x=var[v];e=end[v];ls=[var[w] for w in ns]
            add([-e,x]);add([-x,*ls])
            for t in combinations(ls,3):add([-x,*[-i for i in t]])
            for u,w in combinations(ls,2):add([-e,-u,-w])
            for i in range(len(ls)):add([-x,e,*ls[:i],*ls[i+1:]])
        if desired%2:
            phase=pool.id("major parity")
            for p in (0,1):
                for v in nodes:
                    if v.bit_count()%2==p:add([phase if p else -phase,-end[v]])
            # Exactly two endpoints have the specified parity. The counts
            # follow for any path, and also for any disjoint even cycles.
        squares=0
        for v in nodes:
            for a,b in combinations(range(9),2):
                mask=(1<<a)|(1<<b)
                if v&mask:continue
                square=[v,v^(1<<a),v^(1<<b),v^mask]
                if all(w in possible for w in square):add([-var[w] for w in square]);squares+=1
        status="OPEN";answer=None
        while True:
            remaining=budget-sat.accum_stats()["conflicts"]
            if remaining<=0:break
            sat.conf_budget(remaining);value=sat.solve_limited()
            if value is not True:
                status="UNSAT" if value is False else "OPEN";break
            pos=set(sat.get_model());S={v for v in nodes if var[v] in pos}
            adj={v:set(graph[v])&S for v in S};tips=[v for v in S if len(adj[v])==1]
            assert len(S)==desired and len(tips)==2 and all(len(t) in (1,2) for t in adj.values())
            walk=[tips[0]];visited=set(walk)
            while adj[walk[-1]]-visited:
                v=(adj[walk[-1]]-visited).pop();walk.append(v);visited.add(v)
            if len(walk)==desired:
                assert not defects(walk);answer=walk;status="FOUND";break
            other=S-visited
            while other:
                v=other.pop();C={v};todo=[v]
                while todo:
                    ns=adj[todo.pop()]&other;other-=ns;C|=ns;todo.extend(ns)
                assert all(len(adj[v]&C)==2 for v in C)
                add([-var[v] for v in sorted(C)]);dynamic.append(sorted(C))
        row=dict(tag=tag,slack=slack,source_distance=d,allowed=len(nodes),target=desired,budget=budget,
                 squares=squares,status=status,stats=sat.accum_stats(),cycles=dynamic,witness=answer)
        if checker and status=="UNSAT":row.update(checked_export(sat,output,cap,checker))
    return row


if __name__=="__main__":
    p=argparse.ArgumentParser()
    for x in ("start","stop","slack"):p.add_argument(x,type=int)
    p.add_argument("--budget",type=int,default=300000);p.add_argument("--checker",type=Path)
    a=p.parse_args();raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    source=json.loads(raw);rows=[]
    assert examine(source[0]["vertex_sequence"],"control",0,200000,None,192)["status"]=="FOUND"
    for i in range(a.start,a.stop):
        r=examine(source[i]["vertex_sequence"],f"{i}-{a.slack}",a.slack,a.budget,
                  a.checker.resolve() if a.checker else None)
        rows.append(dict(index=i,**r))
        if r["status"]=="FOUND":break
    save(Path(f"dual-union-{a.slack}-{a.start}-{a.stop}"+("-checked" if a.checker else "")+".json"),rows)
    print(len(rows),{s:sum(t["status"]==s for t in rows) for s in ("FOUND","OPEN","UNSAT")},flush=True)
