"""Certify a residual rooted Q7 path target after all earlier layers have been fixed."""
import argparse,json
from collections import Counter
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from export_drat import checked_export
from solve import save,defects


def jobs():
    work={}
    for file in sorted(Path(".").glob("free-last-*-4.0.json")):
        for rec in json.loads(file.read_text())["profiles"]:
            for r in rec["open"]:
                root=r["C"][-1]
                domain=tuple(sorted(v^root for v in (set(range(128))-(set(r["A"])|set(r["C"])))|{root}))
                key=(domain,rec["sizes"][3]);work.setdefault(key,[]).append(dict(profile=rec["index"],**r))
    return list(work.items())


def decide(domain,target,budget,tag,checker):
    S=set(domain);graph={v:{v^(1<<b) for b in range(7)}&S for v in S}
    reach={0};todo=[0]
    while todo:
        new=graph[todo.pop()]-reach;reach|=new;todo.extend(new)
    if len(reach)<target:return dict(status="component")
    pool=IDPool();sel={v:pool.id(("vertex",v)) for v in sorted(reach)}
    end={v:pool.id(("end",v)) for v in sorted(reach)};clauses=[];cuts=[]
    with Solver(name="cadical195",with_proof=bool(checker)) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        def eq(ls,k):
            for c in CardEnc.equals(list(ls),bound=k,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        odd=[lit for v,lit in sel.items() if v.bit_count()%2]
        if len(odd)<target//2 or len(sel)-len(odd)<(target+1)//2:return dict(status="parity")
        eq(odd,target//2);eq([lit for v,lit in sel.items() if not v.bit_count()%2],(target+1)//2)
        eq(end.values(),2);add([end[0]])
        for v in sorted(reach):
            x=sel[v];e=end[v];ns=[sel[w] for w in sorted(graph[v])]
            add([-e,x]);add([-x,*ns])
            for tri in combinations(ns,3):add([-x,*[-u for u in tri]])
            for a,b in combinations(ns,2):add([-e,-a,-b])
            for j in range(len(ns)):add([-x,e,*ns[:j],*ns[j+1:]])
            if v and ((target-1-v.bit_count())%2):add([-e])
            for a,b in combinations(range(7),2):
                mask=(1<<a)|(1<<b)
                if v&mask:continue
                square=(v,v^1<<a,v^1<<b,v^mask)
                if all(w in reach for w in square):add([-sel[w] for w in square])
        status="OPEN";witness=None
        while (left:=budget-sat.accum_stats()["conflicts"])>0:
            sat.conf_budget(left);ans=sat.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            pos=set(sat.get_model());used={v for v,x in sel.items() if x in pos}
            q=[0];used.remove(0)
            while (nxt:=graph[q[-1]]&used):
                assert len(nxt)==1;v=nxt.pop();q.append(v);used.remove(v)
            if not used:
                assert len(q)==target and not defects(q);status="FOUND";witness=q;break
            while used:
                v=used.pop();comp={v};queue=[v]
                while queue:
                    new=graph[queue.pop()]&used;used-=new;comp|=new;queue.extend(new)
                assert all(len(graph[v]&comp)==2 for v in comp)
                cuts.append(sorted(comp));add([-sel[v] for v in sorted(comp)])
        out=dict(status=status,path=witness,conflicts=sat.accum_stats()["conflicts"],cuts=cuts)
        if checker and status=="UNSAT":out.update(checked_export(sat,clauses,Path("free-last-proof-"+tag),checker))
    return out


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=100000);p.add_argument("--checker",type=Path);a=p.parse_args()
    todo=jobs();rows=[];file=Path(f"last-certified-{a.first}-{a.stop}-{a.budget}.json")
    ctrl=json.loads(Path("four-layer-190-control.json").read_text())["vertices"]
    arm=[v&127 for v in ctrl if v>>7==2];s=arm[0];ctrl_dom={v^s for v in arm}
    assert decide(ctrl_dom,len(arm),100000,"control",None)["status"]=="FOUND"
    for i,((domain,k),occ) in enumerate(todo[a.first:a.stop],a.first):
        r=decide(domain,k,a.budget,str(i),a.checker.resolve() if a.checker else None)
        if r.get("path"):
            row=occ[0];root=row["C"][-1]
            q=[*row["A"],*[x|128 for x in row["B"]],*[x|384 for x in row["C"]],*[(v^root)|256 for v in r["path"]]]
            assert len(q)==193 and not defects(q);r["vertices"]=q
        rows.append(dict(index=i,target=k,domain=domain,occurrences=len(occ),**r));save(file,rows)
        if r.get("vertices"):break
    print(len(todo),len(rows),Counter(r["status"] for r in rows),flush=True)
