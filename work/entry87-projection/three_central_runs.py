"""Keep the two consecutive central runs in different faces and reconstruct both outer runs."""
import argparse
import json
from collections import Counter
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from punctured_lift import project
from solve import BANK, BANK_HASH, defects, save, sha256
from three_cross_faces import normalize


def catalogue():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    cases={}
    for i,row in enumerate(json.loads(raw)):
        p=row["vertex_sequence"]
        counts=Counter((x^y).bit_length()-1 for x,y in zip(p,p[1:]))
        for axis,val in counts.items():
            if val!=3:continue
            q,(a,b,c)=project(p,axis)
            u=q[a:b+1][::-1];v=q[b:c+1]
            shape=min(normalize(u,v),normalize(v,u))
            assert set(shape[0])&set(shape[1])=={0}
            cases.setdefault(shape,[]).append(dict(entry=i,axis=axis))
    return [dict(middle=s,occurrences=os) for s,os in cases.items()]


def outside_graph(fixed, opposite):
    root=opposite[-1]
    blocked=set(fixed)|{v^(1<<j) for v in fixed for j in range(8)}|(set(opposite)-{root})
    assert root not in blocked
    seen={root};queue=[root]
    while queue:
        v=queue.pop()
        fresh={v^(1<<j) for j in range(8)}-blocked-seen
        seen.update(fresh);queue.extend(fresh)
    return {v:sorted({v^(1<<j) for j in range(8)}&seen) for v in sorted(seen)}


def decide(case,i,target,budget,checker):
    fixed=case["middle"]
    graphs=[outside_graph(fixed[s],fixed[1-s]) for s in (0,1)]
    roots=[fixed[1-s][-1] for s in (0,1)]
    pool=IDPool();clauses=[]
    chosen=[{v:pool.id(("use",s,v)) for v in graphs[s]} for s in (0,1)]
    ends=[{v:pool.id(("end",s,v)) for v in graphs[s]} for s in (0,1)]
    def exact(lits,k):
        clauses.extend(CardEnc.equals(lits,bound=k,vpool=pool,encoding=EncType.totalizer).clauses)
    exact([x for side in chosen for x in side.values()],target-sum(map(len,fixed)))
    for v in graphs[0].keys()&graphs[1].keys():
        clauses.append([-chosen[0][v],-chosen[1][v]])
    for s in (0,1):
        exact(list(ends[s].values()),1);clauses.append([chosen[s][roots[s]]])
        for v,neighbours in graphs[s].items():
            var=chosen[s][v];e=ends[s][v];clauses.append([-e,var])
            deg=[chosen[s][n] for n in neighbours]+[e]
            required=1 if v==roots[s] else 2
            for g in combinations(deg,required+1):clauses.append([-var,*[-t for t in g]])
            for g in combinations(deg,len(deg)-required+1):clauses.append([-var,*g])
    for u in ends[0]:
        for v in ends[1]:
            if (u.bit_count()+v.bit_count())%2!=target%2:
                clauses.append([-ends[0][u],-ends[1][v]])
    status="OPEN";witness=None;cuts=[]
    name=f"three-central-{i}-{target}-{budget}"
    with Solver(name="cadical195",bootstrap_with=clauses,with_proof=bool(checker)) as sat:
        while (left:=budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(left);answer=sat.solve_limited()
            if answer is not True:
                status="UNSAT" if answer is False else "OPEN";break
            positive=set(sat.get_model());arms=[];disconnected=False
            for s in (0,1):
                rest={v for v,var in chosen[s].items() if var in positive}
                arm=[roots[s]];rest.remove(roots[s])
                while fresh:=set(graphs[s][arm[-1]])&rest:
                    assert len(fresh)==1
                    v=fresh.pop();arm.append(v);rest.remove(v)
                arms.append(arm)
                while rest:
                    disconnected=True;v=rest.pop();stack=[v];comp={v}
                    while stack:
                        fresh=set(graphs[s][stack.pop()])&rest
                        stack.extend(fresh);rest-=fresh;comp|=fresh
                    assert all(len(set(graphs[s][v])&comp)==2 for v in comp)
                    cut=[-chosen[s][v] for v in sorted(comp)]
                    cuts.append((s,sorted(comp)));clauses.append(cut);sat.add_clause(cut)
            if not disconnected:
                witness=arms[0][::-1]+[v|256 for v in fixed[1][::-1]]+list(fixed[0])+[v|256 for v in arms[1]]
                assert len(witness)==target and not defects(witness);status="FOUND";break
        result=dict(index=i,status=status,target=target,middle=fixed,domains=list(map(len,graphs)),
                    stats=sat.accum_stats(),witness=witness,cycles=cuts)
        if checker and status=="UNSAT":
            from export_drat import checked_export
            result.update(checked_export(sat,clauses,Path(name+"-proof"),checker))
    save(Path(name+("-checked" if checker else "")+".json"),result)
    print(i,target,status,result["stats"]["conflicts"],flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--start",type=int,default=0);p.add_argument("--stop",type=int,default=0)
    p.add_argument("--target",type=int,choices=(192,193),default=193)
    p.add_argument("--budget",type=int,default=750000);p.add_argument("--checker",type=Path)
    a=p.parse_args();rows=catalogue()
    if not a.stop:
        save(Path("three-central-menu.json"),rows);print(len(rows))
    for i in range(a.start,min(a.stop,len(rows))):
        decide(rows[i],i,a.target,a.budget,a.checker.resolve() if a.checker else None)
