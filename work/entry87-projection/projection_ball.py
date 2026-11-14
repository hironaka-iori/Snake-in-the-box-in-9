"""Decide all single additions or deletions of a projected vertex in one model."""
import argparse, json
from collections import Counter
from itertools import combinations
from pathlib import Path

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from export_drat import checked_export
from punctured_add import possible
from punctured_pit import groups
from punctured_lift import project
from solve import BANK, defects, save


def examine(base, flips, deleting, target, budget, tag, checker):
    base, flips = set(base), set(flips)
    assert flips <= (base if deleting else set(range(256))-base)
    sites = sorted(base if deleting else base | flips)
    if not flips:
        return dict(status="structural", target=target)
    g = {v: sorted({v^(1<<b) for b in range(8)} & set(sites)) for v in sites}
    pool = IDPool()
    changed = {v: pool.id(("change",v)) for v in sorted(flips)}
    selected = {(v,b): pool.id(("select",v,b)) for v in sites for b in (0,1)}
    ends = {(v,b): pool.id(("end",v,b)) for v in sites for b in (0,1)}
    doubles = {}
    # With one deletion at most one original neighbour can disappear.
    for v in sites:
        old = len(set(g[v]) & base)
        if old <= 2+int(deleting):
            doubles[v] = pool.id(("double",v))
    required = target - (len(base) + (-1 if deleting else 1))
    if required < 0 or required > len(doubles):
        return dict(status="capacity",target=target)
    clauses=[]; cuts=[]
    with Solver(name="cadical195",with_proof=bool(checker)) as sat:
        def add(c):
            sat.add_clause(c)
            if checker: clauses.append(c)
        def eq(lits,count):
            for c in CardEnc.equals(list(lits),bound=count,vpool=pool,encoding=EncType.totalizer).clauses: add(c)
        eq(changed.values(),1); eq(doubles.values(),required); eq(ends.values(),2)
        fixed = sorted(base - flips) if deleting else sorted(base)
        if fixed: add([selected[fixed[0],0]])
        phase = pool.id("majority")
        for v in sites:
            a,b=selected[v,0],selected[v,1]
            if v in flips:
                present = -changed[v] if deleting else changed[v]
                add([-present,a,b]); add([present,-a]); add([present,-b])
            else: add([a,b])
            if v in doubles:
                d=doubles[v]; add([-a,-b,d]); add([-d,a]); add([-d,b])
                for w in g[v]:
                    if v<w and w in doubles: add([-d,-doubles[w]])
                for x,y in combinations(g[v],2):
                    for z in (0,1): add([-d,-selected[x,z],-selected[y,z]])
                if deleting and len(g[v])==3:
                    add([-d,*[changed[w] for w in g[v] if w in changed]])
            else: add([-a,-b])
            for z in (0,1):
                s=selected[v,z]; e=ends[v,z]
                neighbours=[selected[v,1-z],*[selected[w,z] for w in g[v]]]
                add([-e,s]); add([-s,*neighbours])
                for triple in combinations(neighbours,3): add([-s,*[-x for x in triple]])
                for x,y in combinations(neighbours,2): add([-e,-x,-y])
                for j in range(len(neighbours)): add([-s,e,*neighbours[:j],*neighbours[j+1:]])
                if target%2: add([-e,phase if (v.bit_count()+z)%2 else -phase])
        for v in sites:
            for a,b in combinations(range(8),2):
                mask=1<<a|1<<b
                if mask & v: continue
                square=(v,v^(1<<a),v^(1<<b),v^mask)
                if all(x in g for x in square):
                    for z in (0,1): add([-selected[x,z] for x in square])
        status="OPEN"; witness=None; change=None
        while (left:=budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(left); answer=sat.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN"; break
            pos=set(sat.get_model())
            whole={v|(z<<8) for (v,z),lit in selected.items() if lit in pos}
            changed_now=[v for v,t in changed.items() if t in pos]
            assert len(changed_now)==1 and {v&255 for v in whole} == base ^ set(changed_now)
            adj={v:{v^(1<<b) for b in range(9)} & whole for v in whole}
            tips=[v for v,g2 in adj.items() if len(g2)==1]
            assert len(tips)==2 and len(whole)==target and all(len(ns) in (1,2) for ns in adj.values())
            q=[tips[0]]; unseen=whole-set(q)
            while adj[q[-1]] & unseen:
                x=next(iter(adj[q[-1]] & unseen)); q.append(x); unseen.remove(x)
            if len(q)==target:
                assert not defects(q); witness=q; change=changed_now[0]; status="FOUND"; break
            while unseen:
                node=unseen.pop(); component={node}; stack=[node]
                while stack:
                    fresh=adj[stack.pop()] & unseen; unseen-=fresh; stack.extend(fresh); component|=fresh
                assert all(len(adj[x] & component)==2 for x in component)
                cuts.append(sorted(component)); add([-selected[x&255,x>>8] for x in sorted(component)])
        out=dict(status=status, target=target, flips=sorted(flips), conflicts=sat.accum_stats()["conflicts"],
                 cuts=cuts, change=change, witness=witness)
        if checker and status=="UNSAT":
            out.update(checked_export(sat,clauses,Path("projection-ball-proof-"+tag),checker))
    return out


def control():
    q=json.loads(BANK.read_bytes())[0]["vertex_sequence"]
    P,_=project(q,0); base=set(P)
    for deleting in (False,True):
        v=min(set(range(256))-base if deleting else base)
        modified=base^{v}
        r=examine(modified,[v],deleting,192,100000,"control",None)
        assert r["status"]=="FOUND" and r["change"]==v


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("first",type=int); p.add_argument("stop",type=int)
    p.add_argument("--remove",action="store_true"); p.add_argument("--budget",type=int,default=20000)
    p.add_argument("--checker",type=Path); a=p.parse_args()
    control(); bank=groups(); mode="remove" if a.remove else "add"
    # Include duplicates here. Each group's conclusion applies independently
    # to all geometrically admissible one-site changes of that group.
    rows=[]
    out=Path(f"projection-ball-{mode}-{a.first}-{a.stop}-{a.budget}.json")
    for i in range(a.first,min(a.stop,len(bank))):
        base=set(bank[i][0])
        flips=[v for v in (sorted(base) if a.remove else sorted(set(range(256))-base)) if not possible(base^{v})[0]]
        r=examine(base,flips,a.remove,193,a.budget,f"{mode}-{i}",a.checker.resolve() if a.checker else None)
        rows.append(dict(index=i,**r))
        if len(rows)%10==0 or r.get("witness"):save(out,rows)
        if r.get("witness"):break
    save(out,rows); print(mode,len(rows),Counter(r["status"] for r in rows),flush=True)
