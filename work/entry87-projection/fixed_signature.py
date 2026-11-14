"""Decide a complete prescribed closed-neighbour signature with the kernel unrestricted."""
import argparse,json
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from signature_parity import signature
from solve import BANK,BANK_HASH,sha256,defects,save


def decide(marked,target,end_parity,reference,budget,omissions=None):
    assert target>=3 and target%2 and signature(marked,9)==set()
    allowed={v for v in range(512) if v in marked or v.bit_count()%2==end_parity}
    pool=IDPool();x={v:pool.id(("site",v)) for v in sorted(allowed)};cuts=[]
    with Solver(name="cadical195") as solver:
        def eq(lits,n):
            solver.append_formula(CardEnc.equals(lits,bound=n,vpool=pool,encoding=EncType.totalizer).clauses)
        for p in (0,1):
            eq([z for v,z in x.items() if v.bit_count()%2==p],target//2+int(p==end_parity))
        eq([x[v] for v in sorted(allowed-marked)],2)
        if omissions is not None:
            forced=len(reference-allowed)
            if forced>omissions:return dict(status="cardinality",cuts=[])
            ls=[-x[v] for v in sorted(reference&allowed)]
            solver.append_formula(CardEnc.atmost(ls,bound=omissions-forced,vpool=pool,encoding=EncType.totalizer).clauses)
        for v in range(512):
            z=x.get(v);ns=[x[w] for j in range(9) if (w:=v^(1<<j)) in x]
            # C(candidate)=marked. The output of each XOR gate is uniquely fixed.
            args=ns+([z] if z else [])
            y=args[0]
            for j,u in enumerate(args[1:]):
                out=pool.id(("xor",v,j))
                for clause in ((y,u,-out),(-y,-u,-out),(y,-u,out),(-y,u,out)):solver.add_clause(clause)
                y=out
            solver.add_clause([y if v in marked else -y])
            if v in marked:solver.add_clause(ns)
            if z:
                for adj in combinations(ns,3 if v in marked else 2):
                    solver.add_clause([-z,*[-t for t in adj]])
                solver.add_clause([-z,*ns])
                if v in marked:
                    for i in range(len(ns)):solver.add_clause([-z,*ns[:i],*ns[i+1:]])
        solver.set_phases([z if v in reference else -z for v,z in x.items()])
        status="OPEN";witness=None
        while (left:=budget-solver.accum_stats()["conflicts"])>0:
            solver.conf_budget(left);answer=solver.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN";break
            positives=set(solver.get_model());whole={v for v,z in x.items() if z in positives}
            assert len(whole)==target and signature(whole,9)==marked
            adj={v:{v^(1<<j) for j in range(9)}&whole for v in whole}
            tips=[v for v,ns in adj.items() if len(ns)==1];assert len(tips)==2 and set(tips)==whole-marked
            q=[tips[0]];rest=whole-set(q)
            while (nxt:=adj[q[-1]]&rest):
                assert len(nxt)==1;w=nxt.pop();q.append(w);rest.remove(w)
            if not rest:
                assert not defects(q);status="FOUND";witness=q;break
            while rest:
                v=rest.pop();part={v};todo=[v]
                while todo:
                    new=adj[todo.pop()]&rest;rest-=new;part|=new;todo.extend(new)
                assert all(len(adj[v]&part)==2 for v in part)
                solver.add_clause([-x[v] for v in sorted(part)]);cuts.append(sorted(part))
        return dict(status=status,conflicts=solver.accum_stats()["conflicts"],cuts=cuts,vertices=witness)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("source",type=int);p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=30000);p.add_argument("--omit",type=int);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    q=json.loads(raw)[a.source]["vertex_sequence"];s=set(q);t=signature(s,9)
    ctrl=set(q[:-1]);assert decide(signature(ctrl,9),191,q[0].bit_count()%2,ctrl,80000,0)["status"]=="FOUND"
    centres=sorted(t,key=lambda v:(min((v^q[0]).bit_count(),(v^q[-1]).bit_count()),v))
    rows=[];file=Path(f"fixed-signature-{a.source}-{a.first}-{a.stop}-{a.budget}-{a.omit}.json")
    for v in centres[a.first:a.stop]:
        marked=t^signature({v},9)
        assert all(sum(x.bit_count()%2==p for x in marked)%4==1 for p in (0,1))
        for p in (0,1):
            result=decide(marked,193,p,s,a.budget,a.omit)
            rows.append(dict(centre=v,end_parity=p,**result));save(file,rows)
            if result.get("vertices"):break
        if rows[-1].get("vertices"):break
    from collections import Counter
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
