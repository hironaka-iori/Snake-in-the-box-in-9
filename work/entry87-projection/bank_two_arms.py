"""Both crossings with fixed bank face. Derive the root parity counts in the two outer arms."""
import argparse
from pathlib import Path
from itertools import combinations
from pysat.solvers import Solver,pysolvers
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from fixed_face import cycle_types
from bank_partner import families
from solve import defects,save


def examine(row,tag,budget,checker,desired=193):
    p=row["parent"];roots={p[0],p[-1]}
    assert len(roots)==2 and p[0]==0
    allowed=set(range(256))-(set(p)-roots);count=desired-len(p)
    graph={v:[w for w in sorted(allowed) if (v^w).bit_count()==1] for v in sorted(allowed)}
    ids=IDPool();sel={v:ids.id(("s",v)) for v in graph};end={v:ids.id(("e",v)) for v in graph}
    clauses=[]
    with Solver(name="cadical195",with_proof=checker is not None) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        def eq(ls,k):
            for c in CardEnc.equals(ls,bound=k,vpool=ids,encoding=EncType.totalizer).clauses:add(c)
        eq(list(sel.values()),count);eq(list(end.values()),2)
        for r in sorted(roots):add([sel[r]])
        # For each value of the outside parity count record the matching
        # parity of the two free endpoints (both odd, both even or split).
        # Both roots are even, so each root's arm contributes one more even
        # vertex precisely when its global endpoint is even.
        evens=[sel[v] for v in graph if v.bit_count()%2==0]
        even_ends=[end[v] for v in graph if v.bit_count()%2==0]
        if desired%2==0:
            # The full path has equal parity counts, and one endpoint of each parity.
            eq(evens,desired//2-sum(v.bit_count()%2 for v in p));eq(even_ends,1)
        elif p[-1].bit_count()%2:
            # An odd root contributes the opposite imbalance. In the
            # odd-sized outside set exactly one of the two arms is odd-sized.
            assert count%2==1
            both_even=ids.id("both_even")
            for value in (0,1):
                for literals,k in ((evens,count//2+value),(even_ends,2*value)):
                    if k in (0,len(literals)):
                        for lit in literals:add(([both_even] if value==0 else [-both_even])+([-lit] if k==0 else [lit]))
                    else:
                        for c in CardEnc.equals(literals,bound=k,vpool=ids,encoding=EncType.totalizer).clauses:
                            add(([both_even] if value==0 else [-both_even])+c)
        elif count%2:
            eq(evens,(count+1)//2);eq(even_ends,1)
        else:
            both=ids.id("both_even")
            for value in (0,1):
                for literals,k in ((evens,count//2+value),(even_ends,2*value)):
                    for c in CardEnc.equals(literals,bound=k,vpool=ids,encoding=EncType.totalizer).clauses:
                        add(([both] if value==0 else [-both])+c)
        for x,neighbors in graph.items():
            v=sel[x];e=end[x];ns=[sel[y] for y in neighbors]
            add([-e,v])
            if x in roots:
                add([e,*ns])
                for y in ns:add([-e,-y])
                for a,b in combinations(ns,2):add([-a,-b])
            else:
                add([-v,*ns])
                for a,b,c in combinations(ns,3):add([-v,-a,-b,-c])
                for a,b in combinations(ns,2):add([-e,-a,-b])
                for i in range(len(ns)):add([-v,e,*ns[:i],*ns[i+1:]])
        seen=set()
        for d in (2,3,4):
            for axes in combinations(range(8),d):
                mask=sum(1<<b for b in axes)
                spread=[sum(((x>>i)&1)<<b for i,b in enumerate(axes)) for x in range(1<<d)]
                for base in range(256):
                    if base&mask:continue
                    for pattern in cycle_types[d]:
                        sites=tuple(sorted(base|spread[t] for t in pattern))
                        if sites in seen or not set(sites)<=allowed:continue
                        assert all(len(set(graph[v]).intersection(sites))==2 for v in sites)
                        seen.add(sites);add([-sel[v] for v in sites])
        extra=[];q=None;status="OPEN"
        while True:
            remain=budget-sat.accum_stats()["conflicts"]
            if remain<=0:break
            sat.conf_budget(remain);answer=sat.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN";break
            pos=set(sat.get_model());chosen={v for v in graph if sel[v] in pos}
            full=set(p)|{v|256 for v in chosen}
            ns={v:{v^(1<<b) for b in range(9)}&full for v in full}
            tips=[v for v in full if len(ns[v])==1]
            assert len(full)==desired and len(tips)==2 and all(len(g) in (1,2) for g in ns.values())
            path=[tips[0]];used=set(path)
            while ns[path[-1]]-used:
                v=(ns[path[-1]]-used).pop();used.add(v);path.append(v)
            if len(path)==desired:
                assert not defects(path);q=path;status="FOUND";break
            rest=full-used
            while rest:
                v=rest.pop();cycle={v};todo=[v]
                while todo:
                    new=ns[todo.pop()]&rest;rest-=new;cycle|=new;todo.extend(new)
                assert all(len(ns[x]&cycle)==2 for x in cycle)
                outer=sorted(v^256 for v in cycle if v>=256);assert outer
                add([-sel[v] for v in outer]);extra.append(outer)
        report=dict(tag=tag,exact_parent=p,roots=sorted(roots),outside_count=count,status=status,
                    budget=budget,stats=sat.accum_stats(),static_cycles=len(seen),dynamic=extra,witness=q)
        if status=="UNSAT" and checker:
            from export_drat import checked_export
            report.update(checked_export(sat,clauses,Path("bank-two-proof-"+tag),checker))
    save(Path("bank-two-"+tag+("-checked" if checker else "")+".json"),report)
    print(tag,status,report["stats"]["conflicts"],flush=True)
    return report


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("length",type=int);p.add_argument("index",type=int)
    p.add_argument("--budget",type=int,default=3000000);p.add_argument("--checker",type=Path)
    a=p.parse_args();examine(families()[a.length][a.index],f"{a.length}-{a.index}",a.budget,
                             a.checker.resolve() if a.checker else None)
