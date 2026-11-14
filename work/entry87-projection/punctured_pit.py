"""Lift any Hamilton ordering of an entire projected bank vertex set."""
import argparse,json
from collections import Counter,defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from export_drat import checked_export
from punctured_lift import project
from solve import BANK,BANK_HASH,sha256,defects,save


def examine(P,tag,budget,checker=None,desired=193):
    sites=sorted(set(P));S=set(sites)
    adj={v:sorted({v^(1<<b) for b in range(8)}&S) for v in sites}
    k=desired-len(sites);candidates={v for v,g in adj.items() if len(g)<=2}
    if len(candidates)<k:
        return dict(status="capacity",possible=len(candidates),required=k)
    pool=IDPool();s={};d={};e={};clauses=[];cuts=[]
    for v in sites:
        if v in candidates:d[v]=pool.id(("double",v))
        for b in (0,1):s[v,b]=pool.id(("layer",v,b));e[v,b]=pool.id(("endpoint",v,b))
    with Solver(name="cadical195",with_proof=checker is not None) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        def eq(lits,k):
            for c in CardEnc.equals(lits,bound=k,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        eq(list(d.values()),k);eq(list(e.values()),2)
        # Swapping the two layers preserves the constraints, so layer zero
        # may be chosen at the least address even if this address is doubled.
        add([s[sites[0],0]])
        for v in sites:
            A=s[v,0];B=s[v,1];add([A,B])
            if v in d:
                add([-A,-B,d[v]]);add([-d[v],A]);add([-d[v],B])
                for w in adj[v]:
                    if w in d and v<w:add([-d[v],-d[w]])
                # Every doubled address already uses its vertical edge.
                # Its degree <=2 in the union of the two selected layers
                # forces distinct sides on its neighbouring addresses.
                if len(adj[v])==2:
                    x,y=adj[v]
                    for b in (0,1):add([-d[v],-s[x,b],-s[y,b]])
            else:add([-A,-B])
            for b in (0,1):
                x=s[v,b];end=e[v,b];ns=[s[v,1-b],*[s[w,b] for w in adj[v]]]
                add([-end,x]);add([-x,*ns])
                for triple in combinations(ns,3):add([-x,*[-u for u in triple]])
                for a,c in combinations(ns,2):add([-end,-a,-c])
                for i in range(len(ns)):add([-x,end,*ns[:i],*ns[i+1:]])
        if desired%2:
            phase=pool.id("majority")
            for (v,b),lit in e.items():add([-lit,phase if (v.bit_count()+b)%2 else -phase])
        square=0
        for v in sites:
            for a,b in combinations(range(8),2):
                mask=(1<<a)|(1<<b)
                if v&mask:continue
                q=(v,v^(1<<a),v^(1<<b),v^mask)
                if set(q)<=S:
                    for z in (0,1):add([-s[x,z] for x in q]);square+=1
        status="OPEN";witness=None
        while True:
            remain=budget-sat.accum_stats()["conflicts"]
            if remain<=0:break
            sat.conf_budget(remain);ans=sat.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            pos=set(sat.get_model());whole={v|(b<<8) for (v,b),lit in s.items() if lit in pos}
            graph={v:{v^(1<<b) for b in range(9)}&whole for v in whole}
            tips=[v for v,g in graph.items() if len(g)==1]
            assert len(whole)==desired and len(tips)==2 and all(len(g) in (1,2) for g in graph.values())
            q=[tips[0]];used=set(q)
            while graph[q[-1]]-used:
                v=(graph[q[-1]]-used).pop();used.add(v);q.append(v)
            if len(used)==desired:
                assert not defects(q);status="FOUND";witness=q;break
            spare=whole-used
            while spare:
                v=spare.pop();component={v};todo=[v]
                while todo:
                    new=graph[todo.pop()]&spare;spare-=new;component|=new;todo.extend(new)
                assert all(len(graph[v]&component)==2 for v in component)
                add([-s[v&255,v>>8] for v in sorted(component)]);cuts.append(sorted(component))
        result=dict(status=status,possible=len(candidates),required=k,squares=square,budget=budget,
                    stats=sat.accum_stats(),dynamic=cuts,witness=witness)
        if checker and status=="UNSAT":result.update(checked_export(sat,clauses,Path("punctured-pit-proof-"+tag),checker))
    return result


def groups():
    data=BANK.read_bytes();assert sha256(data).hexdigest()==BANK_HASH
    seen={}
    for i,r in enumerate(json.loads(data)):
        for axis in range(9):
            P,sw=project(r["vertex_sequence"],axis);key=tuple(sorted(P))
            seen.setdefault(key,[]).append((i,axis))
    return list(seen.items())


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=120000);p.add_argument("--checker",type=Path)
    a=p.parse_args();g=groups();rows=[]
    assert examine(g[0][0],"control",150000,None,192)["status"]=="FOUND"
    for i,(P,occ) in enumerate(g[a.first:a.stop],a.first):
        r=examine(P,str(i),a.budget,a.checker.resolve() if a.checker else None)
        rows.append(dict(index=i,sources=occ,**r))
        if r.get("witness"):break
    save(Path(f"punctured-free-order-{a.first}-{a.stop}"+("-checked" if a.checker else "")+".json"),rows)
    print(len(g),len(rows),Counter(r["status"] for r in rows),flush=True)
