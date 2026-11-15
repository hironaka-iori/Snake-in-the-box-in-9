"""Two labelled outer arms with separate root and endpoint constraints and mixed parity counts."""
import argparse,json
from collections import Counter
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from punctured_lift import project
from regrown_middles import middle_menu
from solve import BANK,BANK_HASH,sha256,defects,save


def labelled(parent,target,budget,split=False):
    assert len(parent)==len(set(parent)) and not defects(parent)
    roots=parent[0],parent[-1];m=target-len(parent);P=set(parent)
    W=sorted(set(range(256))-(P-set(roots)));D=set(W)
    adj={v:sorted({v^(1<<j) for j in range(8)}&D) for v in W}
    pool=IDPool()
    def var(kind):return {v:pool.id((kind,v)) for v in W}
    active=var("active");A=var("first");B=var("second");tip=var("end");first_end=var("first_end")
    choice=pool.id("first_endpoint_even")
    with Solver(name="cadical195") as sat:
        add=sat.add_clause
        def eq(lits,k,gate=None):
            if not 0<=k<=len(lits):add([] if gate is None else [gate]);return
            for c in CardEnc.equals(lits,bound=k,vpool=pool,encoding=EncType.totalizer).clauses:
                add(c if gate is None else [gate,*c])
        eq(list(active.values()),m);eq(list(tip.values()),2);eq(list(first_end.values()),1)
        add([A[roots[0]]]);add([B[roots[1]]])
        for v in W:
            x=active[v];a=A[v];b=B[v];e=tip[v];ae=first_end[v]
            add([-a,x]);add([-b,x]);add([-x,a,b]);add([-a,-b])
            add([-ae,e]);add([-ae,a]);add([-e,-a,ae])
            add([-e,x])
            for w in adj[v]:
                if v<w:add([-a,-B[w]]);add([-b,-A[w]])
            ns=[active[w] for w in adj[v]]
            if v in roots:
                add([e,*ns])
                for w in ns:add([-e,-w])
                for u,w in combinations(ns,2):add([-u,-w])
            else:
                add([-x,*ns])
                for tri in combinations(ns,3):add([-x,*[-w for w in tri]])
                for u,w in combinations(ns,2):add([-e,-u,-w])
                for j in range(len(ns)):add([-x,e,*ns[:j],*ns[j+1:]])
        even=[active[v] for v in W if v.bit_count()%2==0]
        mixed=[A[v] if v.bit_count()%2==0 else B[v] for v in W]
        R=[int(v.bit_count()%2==0) for v in roots]
        targets=[]
        for p in (0,1):
            q=p if target%2 else 1-p
            # The signed sum on each arm is determined by the parities
            # of its own root and its global endpoint, even for a singleton.
            da=R[0]+p-1;db=R[1]+q-1;gate=-choice if p else choice
            assert (m+da+db)%2==0 and (m+da-db)%2==0
            targets.append(((m+da+db)//2,(m+da-db)//2))
            for v in W:
                ev=int(v.bit_count()%2==0)
                if ev!=p:add([gate,-tip[v],-A[v]])
                if ev!=q:add([gate,-tip[v],-B[v]])
        for j,lits in enumerate((even,mixed)):
            if targets[0][j]==targets[1][j]:eq(lits,targets[0][j])
            else:
                for p in (0,1):eq(lits,targets[p][j],-choice if p else choice)
        # A chosen square is a cycle in the outside face.
        for v in W:
            for i,j in combinations(range(8),2):
                mask=(1<<i)|(1<<j)
                if v&mask:continue
                square={v,v^(1<<i),v^(1<<j),v^mask}
                if square<=D:add([-active[w] for w in sorted(square)])
        cuts=[];rows=[];witness=None
        choices=([None,*adj[roots[0]]] if split else [None])
        for arm1 in choices:
            assumptions=[] if not split else [tip[roots[0]] if arm1 is None else active[arm1]]
            start=sat.accum_stats()["conflicts"]
            while True:
                left=budget-(sat.accum_stats()["conflicts"]-start)
                if left<=0:status="OPEN";break
                sat.conf_budget(left);ans=sat.solve_limited(assumptions=assumptions)
                if ans is not True:
                    status="OPEN" if ans is None else "EXHAUSTED";break
                pos=set(sat.get_model());out={v for v in W if active[v] in pos}
                assert len(out)==m and out&P==set(roots)
                full=P|{v|256 for v in out}
                graph={v:{v^(1<<j) for j in range(9)}&full for v in full}
                ends=[v for v,g in graph.items() if len(g)==1]
                assert len(ends)==2 and min(ends)>=256 and all(len(g) in (1,2) for g in graph.values())
                path=[ends[0]];used=set(path)
                while nxt:=graph[path[-1]]-used:
                    assert len(nxt)==1;v=nxt.pop();used.add(v);path.append(v)
                if len(path)==target:
                    assert not defects(path);status="FOUND";witness=path;break
                rest=full-used
                while rest:
                    v=rest.pop();cycle={v};stack=[v]
                    while stack:
                        fresh=graph[stack.pop()]&rest;cycle|=fresh;rest-=fresh;stack.extend(fresh)
                    assert min(cycle)>=256 and all(len(graph[v]&cycle)==2 for v in cycle)
                    c=sorted(v&255 for v in cycle);add([-active[v] for v in c]);cuts.append(c)
            rows.append(dict(start_neighbour=arm1,status=status,conflicts=sat.accum_stats()["conflicts"]-start))
            if witness:break
    return dict(status="FOUND" if witness else ("OPEN" if any(r["status"]=="OPEN" for r in rows) else "EXHAUSTED"),
                roots=roots,outside=m,cases=rows,cut_cycles=cuts,witness=witness)


def source_control():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    for row in json.loads(raw):
        path=row["vertex_sequence"]
        for axis in range(9):
            P,sw=project(path,axis)
            if len(sw)==2:
                p=P[sw[0]:sw[1]+1]
                return p


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=150000);p.add_argument("--split",action="store_true");a=p.parse_args()
    pos=labelled(source_control(),192,600000)
    assert pos["status"]=="FOUND" and not defects(pos["witness"])
    paths=middle_menu()
    for i in range(a.first,a.stop):
        r=labelled(paths[i],193,a.budget,a.split)
        save(Path(f"labelled-arms-{i}-{a.budget}-{int(a.split)}.json"),dict(index=i,control=pos,**r))
        print(i,r["status"],sum(z["conflicts"] for z in r["cases"]),flush=True)
        if r["witness"]:break
