"""Search prescribed changes of an unordered projection, with all face assignments free."""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from punctured_lift import project
from solve import BANK,BANK_HASH,defects,save,sha256


def search(W,budget,control=False,roots=None,removals=1,crossings=1,root_pairs=None):
    W=set(W);n=8;holes=set(range(256))-W
    adj=[[v^(1<<b) for b in range(n)] for v in range(256)]
    removed=0 if control else removals
    added=0 if control else 193-crossings-len(W)+removals
    assert 1<=crossings<=6 and added>=0
    root_candidates=[v for v in range(256) if len(set(adj[v])&W)<=2+removed]
    if len(root_candidates)<crossings:
        return [dict(root=None,status="EXHAUSTED",reason="too few possible doubled addresses",
                     candidates=root_candidates,witness=None,conflicts=0,cycle_cuts=0)]
    pool=IDPool()
    occupied=[pool.id(("used",v)) for v in range(256)]
    face=[[pool.id(("face",b,v)) for v in range(256)] for b in range(2)]
    tip=[[pool.id(("end",b,v)) for v in range(256)] for b in range(2)]
    hinge={v:pool.id(("hinge",v)) for v in root_candidates}
    with Solver(name="cadical195") as solver:
        add=solver.add_clause
        def eq(lits,k):
            for clause in CardEnc.equals(lits,bound=k,vpool=pool,encoding=EncType.seqcounter).clauses:add(clause)
        eq([-occupied[v] for v in sorted(W)],removed)
        eq([occupied[v] for v in sorted(holes)],added)
        eq(list(hinge.values()),crossings)
        if crossings%2:
            for ts in tip:eq(ts,1)
        else:
            eq(tip[0],2);eq(tip[1],0)
        target=len(W)-removed+added+crossings
        # Both complete-path endpoints have the same cube parity exactly at odd cardinality.
        phase=pool.id("first end parity")
        if crossings%2==0 and target%2==0:
            eq([tip[0][v] for v in range(256) if v.bit_count()%2==0],1)
        else:
            for b in range(2):
                for v in range(256):
                    pv=(v.bit_count()+b)%2
                    val=pv^(int(target%2==0) if b else 0)
                    add([-tip[b][v],phase if val else -phase])
        # Global face exchange allows face zero at a fixed occupied reference.
        if crossings%2:
            ref=min(W);add([-occupied[ref],face[0][ref]])
        for v in range(256):
            x,y=face[0][v],face[1][v];u=occupied[v]
            add([-x,u]);add([-y,u]);add([-u,x,y])
            if v in hinge:
                h=hinge[v];add([-x,-y,h]);add([-h,x]);add([-h,y])
                # Each face has at most 99 vertices, so each arm of a 192/193-site
                # path is nontrivial. An internal crossing has two base neighbours.
                for triple in combinations(adj[v],3):add([-h,*[-occupied[z] for z in triple]])
                if crossings==1:
                    for i in range(8):add([-h,*[occupied[z] for z in adj[v] if z!=adj[v][i]]])
                    for b in range(2):add([-h,-tip[b][v]])
                else:
                    add([-h,*[occupied[z] for z in adj[v]]])
                    for w in adj[v]:
                        if w<v and w in hinge:add([-h,-hinge[w]])
            else:add([-x,-y])
            for b in range(2):
                x=face[b][v];e=tip[b][v]
                ns=[face[b][w] for w in adj[v]]+[face[1-b][v]]
                add([-e,x]);add([-x,*ns])
                for t in combinations(ns,3):add([-x,*[-w for w in t]])
                for i,j in combinations(ns,2):add([-e,-i,-j])
                for i in range(len(ns)):add([-x,e,*ns[:i],*ns[i+1:]])
        for v in range(256):
            for i,j in combinations(range(8),2):
                mask=(1<<i)|(1<<j)
                if v&mask:continue
                sites=(v,v^(1<<i),v^(1<<j),v^mask)
                for b in range(2):add([-face[b][s] for s in sites])
        if crossings==2 and target>131:
            # A common occupied neighbour forces the entire middle arm to have
            # three vertices. The other face holds at most 128 (see the Q4 proof).
            for v,ns in enumerate(adj):
                for r,s in combinations((u for u in ns if u in hinge),2):
                    add([-hinge[r],-hinge[s],-occupied[v]])
        rows=[]
        splits=[(v,None) for v in hinge] if root_pairs is None else root_pairs
        for root,other in splits:
            if roots is not None and root not in roots:continue
            assumptions=[hinge[root]]+([-lit for v,lit in hinge.items() if v<root] if crossings>1 else [])
            if other is not None:
                assert crossings==2 and root<other
                assumptions.append(hinge[other])
            start=solver.accum_stats()["conflicts"];cuts=0;witness=None
            while True:
                left=budget-(solver.accum_stats()["conflicts"]-start)
                if left<=0:status="OPEN";break
                solver.conf_budget(left);status=solver.solve_limited(assumptions=assumptions)
                if status is not True:
                    status="EXHAUSTED" if status is False else "OPEN";break
                true=set(solver.get_model());S={v|(b<<8) for b in range(2) for v in range(256) if face[b][v] in true}
                proj={v&255 for v in S}
                assert len(S)==target and len(W-proj)==removed and len(proj-W)==added
                doubled={v for v in proj if v in S and (v|256) in S}
                assert len(doubled)==crossings and min(doubled)==root
                graph={v:{v^(1<<j) for j in range(9)}&S for v in S}
                ends=[v for v,g in graph.items() if len(g)==1]
                assert len(ends)==2 and all(len(g) in (1,2) for g in graph.values())
                q=[ends[0]];used=set(q)
                while nxt:=graph[q[-1]]-used:
                    v=nxt.pop();q.append(v);used.add(v)
                if len(q)==len(S):
                    assert not defects(q);witness=q;status="FOUND";break
                rem=S-used
                while rem:
                    v=rem.pop();component={v};stack=[v]
                    while stack:
                        extra=graph[stack.pop()]&rem;component.update(extra);stack.extend(extra);rem-=extra
                    assert all(len(graph[v]&component)==2 for v in component)
                    add([-face[v>>8][v&255] for v in sorted(component)]);cuts+=1
            row=dict(root=root,status=status,witness=witness,cycle_cuts=cuts,conflicts=solver.accum_stats()["conflicts"]-start)
            if other is not None:row["second"]=other
            rows.append(row)
            if witness:break
    return rows


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=150000);p.add_argument("--retry-from",type=int)
    p.add_argument("--removals",type=int,default=1);p.add_argument("--root",type=int)
    p.add_argument("--crossings",type=int,choices=range(1,7),default=1);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw)
    for source in range(a.first,a.stop):
        P,sw=project(bank[source]["vertex_sequence"],5);assert len(sw)==1 and len(P)==191
        if a.crossings==1:ctrl=P
        else:
            ctrl=next(trace for row in bank for axis in range(9)
                      for trace,swaps in [project(row["vertex_sequence"],axis)] if len(swaps)==a.crossings)
        pos=search(ctrl,a.budget,True,crossings=a.crossings);assert any(r["witness"] for r in pos)
        suffix=("" if a.removals==1 else f"-remove{a.removals}")+("" if a.crossings==1 else f"-cross{a.crossings}")
        roots={a.root} if a.root is not None else None
        if a.retry_from:
            old=json.loads(Path(f"single-hinge-exchange-{source}-{a.retry_from}{suffix}.json").read_bytes())
            roots={r["root"] for r in old["results"] if r["status"]=="OPEN"}
            if not roots:continue
        result=search(P,a.budget,roots=roots,removals=a.removals,crossings=a.crossings)
        if a.root is not None:suffix+=f"-root{a.root}"
        save(Path(f"single-hinge-exchange-{source}-{a.budget}{suffix}.json"),dict(source=source,axis=5,
             removals=a.removals,crossings=a.crossings,roots=sorted(roots) if roots is not None else None,control=pos,results=result))
        print(source,Counter(r["status"] for r in result),sum(r["conflicts"] for r in result),flush=True)
        if any(r["witness"] for r in result):break
