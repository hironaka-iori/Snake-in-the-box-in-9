"""An exact parity-syndrome repair for a chosen 97-anchor or 96-anchor reference."""
import argparse
from itertools import combinations
from pathlib import Path
from pysat.formula import IDPool
from pysat.solvers import Solver
from pysat.card import EncType,CardEnc
from bank_parity import inputs
from export_drat import checked_export
from solve import defects,save
from syndrome import neighbour_syndrome


def solve(index,p,budget,max_changes,checker):
    base=dict(inputs())[index];old=set(base[p::2]);old_checks=neighbour_syndrome(old)
    target=len(old);caps=target==96
    assert target==97-p
    anchors=[v for v in range(512) if v.bit_count()%2==p]
    others=[v for v in range(512) if v.bit_count()%2!=p]
    pool=IDPool();sel={v:pool.id(("selected",v)) for v in anchors}
    checks={w:pool.id(("change",w)) for w in others}
    use={w:pool.id(("connector or tip",w)) for w in others}
    end={v:pool.id(("endpoint",v)) for v in (others if caps else anchors)}
    clauses=[];dynamic=[]
    with Solver(name="cadical195",with_proof=checker is not None) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        def card(lits,k,method):
            for c in method(lits,bound=k,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        # The checks are the independent perturbation variables. Their number
        # must be even since both the old and new anchor classes have equal size.
        card(list(checks.values()),max_changes,CardEnc.atmost)
        card(list(sel.values()),target,CardEnc.equals)
        card(list(end.values()),2,CardEnc.equals)
        # D^2 is the identity. Each selected-anchor bit is its old value XOR
        # the changed checks on its nine neighbours.
        for v in anchors:
            prev=None
            for j in range(9):
                lit=checks[v^(1<<j)]
                if prev is None:prev=lit;continue
                nxt=(sel[v] if v not in old else -sel[v]) if j==8 else pool.id(("xor",v,j))
                for c in ([-prev,-lit,-nxt],[prev,lit,-nxt],[prev,-lit,nxt],[-prev,lit,nxt]):add(c)
                prev=nxt
        def set_degree(s,e,ns):
            if e:add([-e,s])
            add([-s,*ns])
            for triple in combinations(ns,3):add([-s,*[-v for v in triple]])
            if e:
                for x,y in combinations(ns,2):add([-e,-x,-y])
            for i in range(len(ns)):add([-s]+([e] if e else [])+ns[:i]+ns[i+1:])
        for v in anchors:set_degree(sel[v],end.get(v),[use[v^(1<<b)] for b in range(9)])
        for w in others:set_degree(use[w],end.get(w),[sel[w^(1<<b)] for b in range(9)])
        status="OPEN";witness=None
        while True:
            remaining=budget-sat.accum_stats()["conflicts"]
            if remaining<=0:break
            sat.conf_budget(remaining);ans=sat.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            pos=set(sat.get_model())
            A={v for v in anchors if sel[v] in pos};B={v for v in others if use[v] in pos}
            assert len(A|B)==193 and len(neighbour_syndrome(A)^old_checks)<=max_changes
            S=A|B;adj={v:{v^(1<<b) for b in range(9)}&S for v in S}
            tips=[v for v in S if len(adj[v])==1];assert len(tips)==2
            path=[min(tips)];seen=set(path)
            while adj[path[-1]]-seen:
                v=(adj[path[-1]]-seen).pop();path.append(v);seen.add(v)
            if len(path)==193:
                assert not defects(path);witness=path;status="FOUND";break
            rest=S-seen
            while rest:
                seed=rest.pop();comp={seed};todo=[seed]
                while todo:
                    near=adj[todo.pop()]&rest;rest-=near;comp|=near;todo.extend(near)
                assert all(len(adj[v]&comp)==2 for v in comp)
                add([-(sel[v] if v in sel else use[v]) for v in sorted(comp)])
                dynamic.append(sorted(comp))
        row=dict(index=index,parity=p,changes=max_changes,budget=budget,status=status,
                 stats=sat.accum_stats(),dynamic=dynamic,witness=witness)
        tag=f"{index}-{p}-{max_changes}"
        if checker and status=="UNSAT":
            row.update(checked_export(sat,clauses,Path("target-surgery-proof-"+tag),checker))
    save(Path("target-surgery-"+tag+("-checked" if checker else "")+".json"),row)
    print(tag,status,row["stats"]["conflicts"],len(dynamic),flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("index",type=int);p.add_argument("parity",type=int);p.add_argument("changes",type=int)
    p.add_argument("--budget",type=int,default=250000);p.add_argument("--checker",type=Path)
    a=p.parse_args();solve(a.index,a.parity,a.budget,a.changes,a.checker.resolve() if a.checker else None)
