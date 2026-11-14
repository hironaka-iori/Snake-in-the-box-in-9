"""Use the quotient graph on one parity class as an exact obstruction to a 192-edge path.

Both endpoints lie on the 97-member side. The 96 opposite sites are unrestricted.
For a candidate 97-set, the sites with two neighbours give the edges of an ordinary
graph on 97 anchors. A Hamilton path is necessary and sufficient.
"""
import argparse,json
from collections import Counter
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from bank_parity import inputs
from solve import BANK,defects,save
from export_drat import checked_export


def solve_radius(anchor,remove,allowed,budget,limit,target_size=97,short=False,checker=None,tag=""):
    # Search many anchor edits jointly. A selected anchor needs at least one
    # bridge; all but the two endpoints need at least two distinct incidences.
    # The full Q9 path checker below tests the actual all-vertex condition.
    A=set(anchor);U=sorted(A|set(allowed));parity=U[0].bit_count()%2
    assert len(A)==target_size and all(v.bit_count()%2==parity for v in U)
    pool=IDPool();x={v:pool.id(("anchor",v)) for v in U}
    odd=[v for v in range(512) if v.bit_count()%2!=parity]
    target_other=target_size+(1 if short else -1)
    z={v:pool.id(("bridge",v)) for v in odd};ends={v:pool.id(("end",v)) for v in (odd if short else U)}
    with Solver(name="cadical195",with_proof=checker is not None) as s:
        clauses=[]
        def add(c):
            s.add_clause(c)
            if checker:clauses.append(c)
        def eq(lits,n):
            for c in CardEnc.equals(list(lits),bound=n,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        eq([-x[v] for v in sorted(A)],remove);eq([x[v] for v in U if v not in A],remove)
        eq(ends.values(),2)
        def degree(h,ns,e):
            add([-h,*ns])
            if e:add([-e,h])
            for a,b,c in combinations(ns,3):add([-h,-a,-b,-c])
            if e:
                for a,b in combinations(ns,2):add([-e,-a,-b])
            for j in range(len(ns)):
                add([-h,*([e] if e else []),*ns[:j],*ns[j+1:]])
        for w in odd:
            degree(z[w],[x[y] for j in range(9) if (y:=w^(1<<j)) in x],ends.get(w))
        for v in U:degree(x[v],[z[v^(1<<j)] for j in range(9)],ends.get(v))
        # Handshaking forces exactly 96 bridge vertices. Stating this
        # explicitly can help when the candidate anchor domain is broad.
        eq(z.values(),target_other)
        best=None;tested=0;status="OPEN";cuts=[]
        while tested<limit and (left:=budget-s.accum_stats()["conflicts"])>0:
            s.conf_budget(left);ans=s.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            pos=set(s.get_model());chosen={v for v,t in x.items() if t in pos};bridges={v for v,t in z.items() if t in pos}
            assert len(chosen)==target_size and len(bridges)==target_other
            whole=chosen|bridges;graph={v:{v^(1<<j) for j in range(9)}&whole for v in whole}
            tips=[v for v,ns in graph.items() if len(ns)==1];assert len(tips)==2 and set(tips)<=(bridges if short else chosen)
            q=[tips[0]];rest=whole-{tips[0]}
            while (ns:=graph[q[-1]]&rest):
                assert len(ns)==1;w=ns.pop();q.append(w);rest.remove(w)
            if len(q)==target_size+target_other:
                assert not defects(q);best=q;status="FOUND";break
            tested+=1
            while rest:
                v=rest.pop();comp={v};todo=[v]
                while todo:
                    fresh=graph[todo.pop()]&rest;rest-=fresh;comp|=fresh;todo.extend(fresh)
                assert all(len(graph[v]&comp)==2 for v in comp)
                # This is a genuine Q9 cycle, which no induced path can contain.
                add([-x[v] if v in chosen else -z[v] for v in sorted(comp)]);cuts.append(sorted(comp))
        out=dict(status=status,source_omissions=remove,extra_addresses=len(set(U)-A),models=tested,
                 conflicts=s.accum_stats()["conflicts"],cycles=cuts,vertices=best)
        if checker and status=="UNSAT":out.update(checked_export(s,clauses,Path("anchor-radius-proof-"+tag),checker))
        return out


def relevant(A,i,j,radius):
    axis=[v for v in range(512) if v.bit_count()%2==next(iter(A)).bit_count()%2 and v not in A]
    return {v for v in axis if min((v^i).bit_count(),(v^j).bit_count())<=radius}


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int);p.add_argument("remove",type=int)
    p.add_argument("--radius",type=int,default=9);p.add_argument("--budget",type=int,default=150000)
    p.add_argument("--limit",type=int,default=500);p.add_argument("--short",action="store_true")
    p.add_argument("--checker",type=Path);a=p.parse_args();rows=[]
    source=json.loads(BANK.read_bytes())[0]["vertex_sequence"][:191]
    assert solve_radius(set(source[int(a.short)::2]),0,[],100000,500,95 if a.short else 96,a.short)["status"]=="FOUND"
    suffix=("-short" if a.short else "")+("-checked" if a.checker else "")
    file=Path(f"anchor-radius-{a.remove}-{a.radius}-{a.first}-{a.stop}-{a.budget}{suffix}.json")
    for k,q in inputs():
        if not a.first<=k<a.stop:continue
        s,t,u,v=defects(q)[0];A=set(q[int(a.short)::2]);options=relevant(A,u,v,a.radius)
        if len(options)<a.remove:r=dict(status="capacity",extra_addresses=len(options))
        else:r=solve_radius(A,a.remove,options,a.budget,a.limit,len(A),a.short,
                            a.checker.resolve() if a.checker else None,f"{k}-{a.remove}-{a.radius}-{int(a.short)}")
        rows.append(dict(index=k,**r));save(file,rows)
        if r.get("vertices"):break
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
