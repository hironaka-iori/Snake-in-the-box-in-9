"""Reconstruct a cube snake from its seven-dimensional ordered projection and square fibres."""
import argparse, json
from collections import Counter, deque
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from export_drat import checked_export
from solve import BANK, BANK_HASH, sha256, defects, save


PATTERNS=[(v,) for v in range(4)]
for v in range(4):
    for b in (1,2):
        PATTERNS += [(v,v^b),(v,v^b,v^3)]
MASKS=[sum(1<<v for v in p) for p in PATTERNS]
ALL=(1<<len(PATTERNS))-1


def valid(a,b,kind):
    p,q=PATTERNS[a],PATTERNS[b]; common=MASKS[a]&MASKS[b]
    if kind=="edge":return p[-1]==q[0] and common.bit_count()==1
    if kind=="reverse":return valid(b,a,"edge")
    if kind=="equal":return len(p)==len(q)==1 and p[0]^q[0]==3
    return not common


SUPPORT={kind:[sum(1<<j for j in range(20) if valid(i,j,kind)) for i in range(20)]
         for kind in ("edge","reverse","equal","chord")}


def members(bits):
    while bits:
        bit=bits&-bits;yield bit.bit_length()-1;bits^=bit


def project_square(path,axes):
    keep=[i for i in range(9) if i not in axes]
    trace=[];shapes=[]
    for v in path:
        col=sum(((v>>b)&1)<<i for i,b in enumerate(keep))
        z=sum(((v>>b)&1)<<i for i,b in enumerate(axes))
        if not trace or trace[-1]!=col:trace.append(col);shapes.append([])
        shapes[-1].append(z)
    shift=shapes[0][0]
    choices=[PATTERNS.index(tuple(z^shift for z in s)) for s in shapes]
    assert set(Counter(trace).values())<={1,2}
    return trace,choices


def requirements(trace):
    rows=[[] for _ in trace]; locations={}
    for j,col in enumerate(trace):
        for v in (col,*[col^(1<<b) for b in range(7)]):
            for i in locations.get(v,()):
                kind="equal" if v==col else "edge" if j==i+1 else "chord"
                rows[i].append((j,kind))
                rows[j].append((i,"reverse" if kind=="edge" else kind))
        locations.setdefault(col,[]).append(j)
    assert all((a^b).bit_count()==1 for a,b in zip(trace,trace[1:]))
    return rows


def reduce(rows):
    domains=[ALL]*len(rows); domains[0]=sum(1<<i for i,p in enumerate(PATTERNS) if p[0]==0)
    todo=deque(range(len(rows))); queued=set(todo)
    while todo:
        j=todo.popleft();queued.remove(j)
        for i,k in rows[j]:
            rev={"edge":"reverse","reverse":"edge"}.get(k,k)
            allowed=sum(1<<v for v in members(domains[i]) if SUPPORT[rev][v]&domains[j])
            if allowed!=domains[i]:
                if not allowed:return None
                domains[i]=allowed
                if i not in queued:todo.append(i);queued.add(i)
    return domains


def lift(trace,choices):
    return [col|(z<<7) for col,a in zip(trace,choices) for z in PATTERNS[a]]


def search(trace,original,budget,tag,checker=None,target=193):
    graph=requirements(trace);dom=reduce(graph)
    if original is not None:
        assert not defects(lift(trace,original))
        assert all(dom[i]>>a&1 for i,a in enumerate(original))
        assert all(valid(original[i],original[j],k) for i,ns in enumerate(graph) for j,k in ns)
    if dom is None:return dict(status="unsupported")
    maxlen=sum(max(len(PATTERNS[v]) for v in members(d)) for d in dom)
    basic=dict(visits=len(trace),repeats=len(trace)-len(set(trace)),upper=maxlen)
    if maxlen<target:return dict(status="capacity",**basic)
    pool=IDPool();clauses=[];choice=[{v:pool.id((i,v)) for v in members(d)} for i,d in enumerate(dom)]
    with Solver(name="cadical195",with_proof=bool(checker)) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        extra=[];minimum=len(trace)
        for i,menu in enumerate(choice):
            add(list(menu.values()))
            for x,y in combinations(menu.values(),2):add([-x,-y])
            for count in (2,3):
                yes=[lit for v,lit in menu.items() if len(PATTERNS[v])>=count]
                if not yes:continue
                if len(yes)==len(menu):minimum+=1;continue
                flag=pool.id(("atleast",i,count));extra.append(flag)
                add([-flag,*yes])
                for x in yes:add([-x,flag])
        if target>minimum:
            for c in CardEnc.atleast(extra,bound=target-minimum,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        for i,ns in enumerate(graph):
            for j,k in ns:
                for v,lit in choice[i].items():
                    support=SUPPORT[k][v]&dom[j]
                    if support!=dom[j]:add([-lit,*[choice[j][x] for x in members(support)]])
        sat.conf_budget(budget);ans=sat.solve_limited()
        out=dict(status="UNSAT" if ans is False else "OPEN" if ans is None else "FOUND",
                 conflicts=sat.accum_stats()["conflicts"],**basic)
        if ans is True:
            pos=set(sat.get_model()); picked=[next(a for a,t in menu.items() if t in pos) for menu in choice]
            q=lift(trace,picked); assert len(q)>=target and not defects(q)
            out.update(vertices=q,edges=len(q)-1)
        if checker and ans is False:out.update(checked_export(sat,clauses,Path("square-fibre-proof-"+tag),checker))
    return out


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=18000);p.add_argument("--checker",type=Path);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;known=json.loads(raw)
    control,old=project_square(known[0]["vertex_sequence"],(0,8))
    assert search(control,old,200000,"control",None,192)["status"]=="FOUND"
    file=Path(f"square-fibres-{a.first}-{a.stop}-{a.budget}.json");rows=[]
    for i in range(a.first,a.stop):
        for axes in combinations(range(9),2):
            trace,old=project_square(known[i]["vertex_sequence"],axes)
            r=search(trace,old,a.budget,f"{i}-{axes[0]}-{axes[1]}",a.checker.resolve() if a.checker else None)
            rows.append(dict(source=i,axes=axes,**r))
            if r["status"]=="FOUND":break
        save(file,rows)
        if rows[-1]["status"]=="FOUND":break
    print(len(rows),Counter(r["status"] for r in rows),flush=True)
