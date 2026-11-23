from itertools import combinations
from collections import defaultdict,Counter
from pathlib import Path
import sys,time,json
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
D=Path(__file__).resolve().parent
def solve(sites,T,goal,cap):
    E=set(sites);m=len(E);assert m==goal//2+1
    lut=[0]
    for g in T[1:]:lut += [x^g^T[0] for x in lut]
    assert len(set(lut))==256
    physical={v:i|((i.bit_count()%2)<<8) for i,v in enumerate(lut)}
    hosting={};ports=defaultdict(list);graph=defaultdict(set)
    for z in range(256):
        vs=sorted(y for t in T if (y:=z^t) in E)
        if len(vs)==2:
            a,b=vs;hosting.setdefault((a,b),z);graph[a].add(b);graph[b].add(a)
        if len(vs)==1:ports[vs[0]].append(z)
    if len(hosting)<m-1 or (goal%2 and not ports):return 'PRUNED',None
    ghost=256;pool=IDPool();ed={};at=defaultdict(list);cls=[]
    for a,b in [*hosting,*[(x,ghost) for x in E]]:
        v=pool.id();ed[a,b]=v;at[a].append(v);at[b].append(v)
    for a,links in at.items():
        if len(links)<2:return 'PRUNED',None
        cls.extend(CardEnc.equals(links,bound=2,vpool=pool,encoding=EncType.seqcounter).clauses)
    if goal%2:cls.append([ed[x,ghost] for x in ports])
    with Cadical195(bootstrap_with=cls) as sat:
        while True:
            remain=cap-sat.accum_stats()['conflicts']
            if remain<=0:return 'UNKNOWN',None
            sat.conf_budget(remain);r=sat.solve_limited()
            if r!=True:return ('UNKNOWN' if r is None else 'UNSAT'),None
            model=set(sat.get_model());nb=defaultdict(list)
            for (a,b),v in ed.items():
                if v in model:nb[a].append(b);nb[b].append(a)
            order=[ghost];prev=-1;x=ghost
            while True:
                y=next(q for q in nb[x] if q!=prev)
                if y==ghost:break
                order.append(y);prev,x=x,y
            if len(order)==m+1:break
            used=set(order);sat.add_clause([v for (a,b),v in ed.items() if (a in used)!=(b in used)])
    h=order[1:]
    if goal%2 and h[-1] not in ports:h.reverse()
    odd=lambda z:physical[z^T[0]]^256
    p=[physical[h[0]]]
    for a,b in zip(h,h[1:]):p.extend([odd(hosting[min(a,b),max(a,b)]),physical[b]])
    if goal%2:p.append(odd(ports[h[-1]][0]))
    assert len(p)==goal+1 and len(set(p))==len(p) and all(((u^v).bit_count()==1)==(j==i+1) for j,u in enumerate(p) for i,v in enumerate(p[:j]))
    return 'FOUND',p
def main():
    mode=sys.argv[1]
    if mode=='control':
        from random import Random
        rng=Random(1466)
        for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()[:16]):
            p=[0]
            for a in w:p.append(p[-1]^1<<int(a))
            goal=190+(i%2);p=p[:goal+1];sp={0};ds=[]
            while len(ds)<8:
                a=rng.randrange(1,256)
                if a not in sp:ds.append(a);sp.update({x^a for x in sp})
            off=rng.randrange(256);T=[off,*[off^a for a in ds]];lut=[0]
            for a in ds:lut += [z^a for z in lut]
            sites=[lut[x&255] for x in p[::2]]
            st,path=solve(sites,T,goal,150000);print(json.dumps(dict(case=i,goal=goal,status=st,path=path)),flush=True)
    else:
        goal,nrows,cap=map(int,sys.argv[1:]);file=D/f'candidates{goal}.log';seen=0
        with file.open() as fp:
            while True:
                line=fp.readline()
                if not line:
                    time.sleep(2);continue
                x=line.split()
                if x[0]=='R' and int(x[1])==nrows-1:break
                if x[0]!='C':continue
                T=list(map(int,x[3:12]));sites=list(map(int,x[13:]));st,p=solve(sites,T,goal,cap)
                print(json.dumps(dict(id=seen,restart=x[1],step=x[2],T=T,sites=sites,status=st,path=p)),flush=True);seen+=1
                if p:break
if __name__=='__main__':main()
