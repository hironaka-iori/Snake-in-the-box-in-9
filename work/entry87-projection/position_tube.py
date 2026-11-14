"""Direct positional Hamming-ball repair of an arbitrary one-chord near-walk."""
import argparse,json
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from solve import BANK,BANK_HASH,defects,save,sha256


def tube(q,region,budget,anchor_start,seed):
    n=len(q);domain=[]
    masks=[0,*[(1<<a)|(1<<b) for a,b in combinations(range(9),2)]]
    for i,v in enumerate(q):
        ds={v^m for m in masks} if i in region and not(i==0 and anchor_start) else {v}
        domain.append(ds)
    # Fixed vertices propagate all chord exclusions and consecutive edges.
    changed=True
    while changed:
        changed=False
        fixed=[(j,next(iter(ds))) for j,ds in enumerate(domain) if len(ds)==1]
        for i,ds in enumerate(domain):
            new=set(ds)
            for j,w in fixed:
                if i==j:continue
                if abs(i-j)==1:new={v for v in new if (v^w).bit_count()==1}
                else:new={v for v in new if (v^w).bit_count()>=2}
            for j in (i-1,i+1):
                if 0<=j<n:new={v for v in new if any((v^w).bit_count()==1 for w in domain[j])}
            if not new:return dict(status="domain contradiction",position=i)
            if new!=ds:domain[i]=new;changed=True
    pool=IDPool();x=[{v:pool.id(("at",i,v)) for v in sorted(ds)} for i,ds in enumerate(domain)]
    with Solver(name="cadical195") as sat:
        if seed:sat.configure({"seed":seed})
        for menu in x:
            for c in CardEnc.equals(list(menu.values()),bound=1,vpool=pool,encoding=EncType.seqcounter).clauses:sat.add_clause(c)
        for j in range(1,n):
            for i,k in ((j-1,j),(j,j-1)):
                for v,lit in x[i].items():
                    permitted=[x[k][y] for b in range(9) if (y:=v^(1<<b)) in x[k]]
                    sat.add_clause([-lit,*permitted])
        for j,menu in enumerate(x):
            for i in range(j-1):
                prev=x[i]
                if len(menu)==1 or len(prev)==1:continue
                for v,lit in menu.items():
                    if (j-i)%2==0:
                        if v in prev:sat.add_clause([-lit,-prev[v]])
                    else:
                        for b in range(9):
                            u=v^(1<<b)
                            if u in prev:sat.add_clause([-lit,-prev[u]])
        sat.set_phases([t if v==q[i] else -t for i,menu in enumerate(x) for v,t in menu.items()])
        sat.conf_budget(budget);yes=sat.solve_limited()
        out=dict(status="UNSAT" if yes is False else "OPEN" if yes is None else "FOUND",
                 conflicts=sat.accum_stats()["conflicts"],live_positions=sum(len(m)>1 for m in x),
                 remaining_choices=sum(map(len,x)))
        if yes:
            pos=set(sat.get_model());path=[next(v for v,lit in menu.items() if lit in pos) for menu in x]
            assert len(path)==n and not defects(path)
            assert all((v^q[i]).bit_count() in (0,2) for i,v in enumerate(path))
            out.update(vertices=path,changes=[i for i,v in enumerate(path) if v!=q[i]])
        return out


def positions(q,width,s,t,style):
    if style=="all":return set(range(len(q)))
    if style=="ends":return {i for i in range(len(q)) if i<width or i>=len(q)-width}
    if style=="chord":return {i for i in range(len(q)) if min(abs(s-i),abs(t-i))<=width}
    return {i for i,v in enumerate(q) if min((v^q[s]).bit_count(),(v^q[t]).bit_count())<=width}


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("style",choices=("all","ends","chord","geometric"));p.add_argument("width",type=int)
    p.add_argument("--budget",type=int,default=60000);p.add_argument("--no-anchor",action="store_true")
    p.add_argument("--seed",type=int,default=0);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;bank=json.loads(raw);items=json.loads(Path("bank-pivots.json").read_text())
    # Deliberately move one vertex to another same-parity site; the original
    # is in its domain and can be recovered with all other positions fixed.
    ctrl=bank[0]["vertex_sequence"].copy();ctrl[31]^=3
    assert defects(ctrl) and tube(ctrl,{31},20000,True,0)["status"]=="FOUND"
    rows=[];file=Path(f"position-tube-{a.style}-{a.width}-{a.first}-{a.stop}-{a.budget}-{int(a.no_anchor)}-{a.seed}.json")
    for k in range(a.first,min(a.stop,len(items))):
        r=items[k];q=bank[r["entry"]]["vertex_sequence"];j=r["insertion"];m=1<<r["flip"]
        q=q[:j+1]+[v^m for v in q[j:]];s,t=r["chord"][:2]
        assert defects(q)==[tuple(r["chord"])]
        region=positions(q,a.width,s,t,a.style)
        ans=tube(q,region,a.budget,not a.no_anchor,a.seed)
        rows.append(dict(index=k,region=len(region),**ans));save(file,rows)
        if ans["status"]=="FOUND":break
    print(len(rows),rows[-1]["status"],flush=True)
