"""Optimize the two free Q7 layers independently after placing two nonadjacent anchor paths."""
import argparse,json,subprocess,time
import heapq
from collections import Counter
from itertools import combinations
from pathlib import Path
from ortools.sat.python import cp_model
from four_layer_bank import menus
from solve import defects,save


def arm(domain,root,tip,seconds,seed):
    domain=set(domain);graph={v:{v^(1<<i) for i in range(7)}&domain for v in domain}
    # The path lies in the root component. Remove any other components before modelling.
    active={root};stack=[root]
    while stack:
        fresh=graph[stack.pop()]-active;active|=fresh;stack.extend(fresh)
    if tip is not None and tip not in active:return dict(status="inaccessible",upper=0)
    nodes=sorted(active);m=cp_model.CpModel()
    sel={v:m.new_bool_var(f"x{v}") for v in nodes}
    ends={v:m.new_bool_var(f"e{v}") for v in nodes}
    m.add(sum(ends.values())==2);m.add(ends[root]==1)
    if tip is not None:m.add(ends[tip]==1)
    for v in nodes:
        m.add(ends[v]<=sel[v])
        m.add(sum(sel[w] for w in graph[v])==2-ends[v]).only_enforce_if(sel[v])
        for a,b in combinations(range(7),2):
            mask=1<<a|1<<b
            if v&mask:continue
            square=(v,v^(1<<a),v^(1<<b),v^mask)
            if all(w in sel for w in square):m.add(sum(sel[w] for w in square)<=3)
    m.maximize(sum(sel.values()));s=cp_model.CpSolver();s.parameters.num_search_workers=1;s.parameters.random_seed=seed
    start=time.monotonic();upper=len(nodes);best=[];answer="OPEN";cuts=0
    while (left:=seconds-time.monotonic()+start)>0:
        s.parameters.max_time_in_seconds=left
        status=s.solve(m)
        if status==cp_model.INFEASIBLE:return dict(status="infeasible",upper=0)
        if status not in (cp_model.OPTIMAL,cp_model.FEASIBLE):break
        upper=min(upper,int(s.best_objective_bound+1e-6))
        used={v for v in nodes if s.value(sel[v])};q=[root];used.remove(root)
        while (fresh:=graph[q[-1]]&used):
            assert len(fresh)==1;v=fresh.pop();q.append(v);used.remove(v)
        assert (tip is None or q[-1]==tip) and not defects(q)
        if len(q)>len(best):best=q
        if not used:
            answer="optimal" if status==cp_model.OPTIMAL else "feasible";break
        while used:
            x=used.pop();comp={x};stack=[x]
            while stack:
                new=graph[stack.pop()]&used;used-=new;comp|=new;stack.extend(new)
            assert all(len(graph[v]&comp)==2 for v in comp)
            m.add(sum(sel[v] for v in comp)<len(comp));cuts+=1
    return dict(status=answer,upper=upper,path=best,cuts=cuts)


def candidates(a):
    forms={s.encode():v for s,v in json.loads(Path("highdim-seven-39.json").read_text())["forms"].items()}
    banks=[menus(forms,n) for n in (a.left,a.third)]
    raw=b"\n".join(x for bag in banks for x in (str(len(bag)).encode(),*bag))
    cmd=[str(Path(a.exe).resolve()),"193",str(a.placements)]
    if a.correlated:cmd.append("correlated")
    program=subprocess.run(cmd,input=raw,capture_output=True,check=True)
    out=[];seen=set()
    for line in program.stdout.splitlines():
        upper,root,b,d,n,*word=map(int,line.split())
        L=word[:n];length=word[n];R=word[n+1:]
        assert len(R)==length and root==L[-1] and {b,d}=={R[0],R[-1]}
        if R[0]!=b:R.reverse()
        assert {b,d}.isdisjoint(L) and root not in R
        key=(tuple(L),tuple(R))
        if key in seen:continue
        seen.add(key)
        out.append((upper,L,R))
    def rank(record):
        upper,L,R=record;free=set(range(128))-(set(L)|set(R))
        # Degree-two chains are easy to use. Penalize crowded vertices whose
        # many incidental edges make the optimistic connectivity bound loose.
        degree=[sum((x^(1<<b)) in free for b in range(7)) for x in free]
        return (len(set(L)&set(R)),upper,sum(1 for d in degree if 1<=d<=3))
    top=heapq.nlargest(a.offset+a.limit,out,key=rank)
    for _,L,R in top:assert not defects(L) and not defects(R)
    return program.stderr.decode().strip(),top


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("left",type=int);p.add_argument("third",type=int)
    p.add_argument("--placements",type=int,default=2500);p.add_argument("--limit",type=int,default=30)
    p.add_argument("--seconds",type=float,default=0.7);p.add_argument("--offset",type=int,default=0)
    p.add_argument("--correlated",action="store_true");p.add_argument("--exe",default="zipper.exe");a=p.parse_args()
    summary,pairs=candidates(a);best=0;rows=[]
    suffix="-correlated" if a.correlated else ""
    file=Path(f"zipper-{a.left}-{a.third}-{a.placements}-{a.offset}-{a.limit}-{a.seconds}{suffix}.json")
    print("placements, usable, colour capacity",summary,flush=True)
    for i,(upper,L,R) in enumerate(pairs[a.offset:a.offset+a.limit],a.offset):
        free=set(range(128))-(set(L)|set(R))
        B=arm(free|{L[-1],R[0]},L[-1],R[0],a.seconds,1)
        D=arm(free|{R[-1]},R[-1],None,a.seconds,7)
        q=None
        if B.get("path") and D.get("path"):
            q=[*L,*[x|128 for x in B["path"]],*[x|384 for x in R],*[x|256 for x in D["path"]]]
            assert not defects(q)
        rows.append(dict(rank=i,upper=upper,left=L,third=R,middle=B,last=D,edges=len(q)-1 if q else None,
                         vertices=q if q and len(q)-1>best else None))
        if q and len(q)-1>best:best=len(q)-1;print("best",i,best,flush=True)
        save(file,dict(survey=summary,results=rows,best_edges=best))
        if q and len(q)>=193:break
    print("done",len(rows),best,flush=True)
