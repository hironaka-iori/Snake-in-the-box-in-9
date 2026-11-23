from itertools import combinations
from pysat.solvers import Cadical195
from pysat.card import CardEnc
from collections import deque
from functools import lru_cache
from time import monotonic
def bits(mask):return [j for j in range(4) if mask>>j&1]
def compatible(a,b):
    verts={j for j in bits(a)}|{4+j for j in bits(b)}
    nb={x:{x^k for k in (1,2,4)}&verts for x in verts}
    if any(len(z)>2 for z in nb.values()):return False
    seen=set()
    for x in verts:
        if x in seen:continue
        todo=[x];part={x}
        for y in todo:
            for z in nb[y]-part:part.add(z);todo.append(z)
        if all(len(nb[y])==2 for y in part):return False
        seen.update(part)
    return True
COMP=[[compatible(a,b) for b in range(15)] for a in range(15)]
@lru_cache(maxsize=None)
def static(a,domain):
    choices=[b for b in domain if COMP[a][b]]
    if not choices:return None
    return tuple((min(b>>j&1 for b in choices),max(b>>j&1 for b in choices)) for j in range(4))
def solve(base,target,loss,domains_minus=None,domains_plus=None,hint=(),dim=9,budget=4000,cycles=50,forced_counts=None):
    t0=monotonic();ncol=1<<(dim-2);volume=4*ncol;h=list(base);assert len(h)==ncol
    gain=target+1-sum(h)+loss
    dom=[];allcols=set(range(ncol))
    up=allcols if domains_plus is None else set(domains_plus);dn=allcols if domains_minus is None else set(domains_minus)
    for i,v in enumerate(h):
        lo=max(0,v-(loss if i in dn else 0));hi=min(3,v+(gain if i in up else 0))
        if forced_counts is not None:lo=hi=forced_counts[i]
        dom.append(tuple(m for m in range(15) if lo<=m.bit_count()<=hi))
    nbs=[[i^(1<<j) for j in range(dim-2)] for i in range(ncol)]
    rec={'gain':gain,'loss':loss,'cuts':0}
    def finish(st,**extra):return dict(rec,status=st,seconds=round(monotonic()-t0,4),**extra)
    if gain<0:return finish('STATIC')
    init=sum(map(len,dom));changed=True
    while changed:
        changed=False
        for c in range(ncol):
            nxt=[]
            for m in dom[c]:
                options=[static(m,dom[j]) for j in nbs[c]]
                if None in options:continue
                if any((m>>(b^1)&1)+(m>>(b^2)&1)+sum(z[b][0] for z in options)>2 or
                       (m>>(b^1)&1)+(m>>(b^2)&1)+sum(z[b][1] for z in options)<1 for b in bits(m)):continue
                nxt.append(m)
            if len(nxt)!=len(dom[c]):dom[c]=tuple(nxt);changed=True
            if not nxt:return finish('STATIC')
    rec.update(states=sum(map(len,dom)),removed=init-sum(map(len,dom)))
    loc=lambda c,b:4*c+b+1
    cnf=[];nv=volume
    def var():
        nonlocal nv
        nv+=1;return nv
    def card(lits,k):
        nonlocal nv
        if k<0 or k>len(lits):cnf.append([]);return
        if k==0:cnf.extend([[-z] for z in lits]);return
        if k==len(lits):cnf.extend([[z] for z in lits]);return
        encoding=CardEnc.equals(lits=lits,bound=k,top_id=nv,encoding=1);nv=encoding.nv;cnf.extend(encoding.clauses)
    masks=[];plus=[];minus=[];cp=cm=0;available=set()
    for c,ds in enumerate(dom):
        row={m:var() for m in ds};masks.append(row);cnf.append(list(row.values()))
        for m,t in row.items():
            for b in range(4):cnf.append([-t,loc(c,b) if m>>b&1 else -loc(c,b)])
        for b in range(4):
            if any(m>>b&1 for m in ds):available.add(4*c+b)
            else:cnf.append([-loc(c,b)])
        for z in range(1,max(3,h[c])+1):
            if z>h[c]:side=plus;pred=lambda m:m.bit_count()>=z
            else:side=minus;pred=lambda m:m.bit_count()<z
            tr=[m for m in ds if pred(m)]
            if not tr:continue
            if len(tr)==len(ds):
                if side is plus:cp+=1
                else:cm+=1
            else:
                mark=var();side.append(mark);cnf.extend([[-t,mark if pred(m) else -mark] for m,t in row.items()])
    card(plus,gain-cp);card(minus,loss-cm)
    # A translation inside every Q2 simultaneously is an automorphism.
    gauge=None
    for c,ds in enumerate(dom):
        if all(m.bit_count()==1 for m in ds):cnf.append([loc(c,0)]);gauge=(c,1);break
        if all(m.bit_count()==3 for m in ds):cnf.append([-loc(c,0)]);gauge=(c,3);break
    for c in range(ncol):
        for j in nbs[c]:
            if j<=c:continue
            for m,v in masks[c].items():
                for b,u in masks[j].items():
                    if not COMP[m][b]:cnf.append([-v,-u])
    endpoints=[];parity=var()
    for v in available:
        x=v+1;ns=[(v^(1<<k))+1 for k in range(dim) if v^(1<<k) in available];ep=var();endpoints.append(ep)
        cnf.extend(([-ep,x],[-x,*ns]))
        cnf.extend([-x,-a,-b,-c] for a,b,c in combinations(ns,3))
        cnf.extend([-ep,-a,-b] for a,b in combinations(ns,2))
        cnf.extend([-x,ep,*ns[:i],*ns[i+1:]] for i in range(len(ns)))
        if target%2==0:cnf.append([-ep,parity if v.bit_count()%2 else -parity])
        for a in range(dim):
            va=v^1<<a
            if va<v or va not in available:continue
            for b in range(a):
                vb=v^1<<b;f=va^1<<b
                if vb>v and vb in available and f in available:cnf.append([-x,-(va+1),-(vb+1),-(f+1)])
    card(endpoints,2);rec.update(vars=nv,clauses=len(cnf))
    H=set(hint)
    if gauge:
        c,k=gauge;options=[b for b in range(4) if ((4*c+b in H)==(k==1))]
        if len(options)==1:H={v^options[0] for v in H}
    with Cadical195(bootstrap_with=cnf) as sat:
        sat.set_phases([z+1 if z in H else -(z+1) for z in available])
        while rec['cuts']<=cycles:
            rem=budget-sat.accum_stats()['conflicts']
            if rem<=0:return finish('UNKNOWN',conflicts=budget)
            sat.conf_budget(rem);ans=sat.solve_limited();n=sat.accum_stats()['conflicts']
            if ans is not True:return finish('UNSAT' if ans is False else 'UNKNOWN',conflicts=n)
            model=set(sat.get_model());s={v for v in available if v+1 in model}
            counts=[sum((4*c+j) in s for j in range(4)) for c in range(ncol)]
            assert sum(counts)==target+1 and sum(max(0,a-b) for a,b in zip(h,counts))==loss and sum(max(0,b-a) for a,b in zip(h,counts))==gain
            graph={v:[v^1<<k for k in range(dim) if v^1<<k in s] for v in s}
            ends=[v for v in s if len(graph[v])==1];assert len(ends)==2 and all(len(g) in (1,2) for g in graph.values())
            p=[ends[0]];u=-1
            while True:
                nx=[v for v in graph[p[-1]] if v!=u]
                if not nx:break
                u=p[-1];p.append(nx[0])
            if len(p)==len(s):return finish('FOUND',conflicts=n,path=p)
            rest=s-set(p)
            while rest:
                comp=[rest.pop()]
                for v in comp:
                    for y in graph[v]:
                        if y in rest:rest.remove(y);comp.append(y)
                sat.add_clause([-(v+1) for v in comp]);rec['cuts']+=1
    return finish('CUT_LIMIT')
