from pathlib import Path
import argparse,sys,json
from itertools import combinations
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
D=Path(__file__).resolve().parent
def load(file):
    records=[]
    for line in file.read_text().splitlines():
        seed,rev,a,b,n,*z=map(int,line.split());p=z[:n];k=z[n];s=z[n+1:];assert len(s)==k;records.append((p,s))
    return records
def run(p,s,target,c,budget,i,log,hint,pins,banned,tip):
    low=set(p+s);roots={p[0],p[-1],s[0],s[-1]};avail=sorted(set(range(256))-(low-roots));ids=IDPool();x={v:ids.id(('x',v)) for v in avail};ep={v:ids.id(('end',v)) for v in avail if c==-1 or (1+v.bit_count())%2==c};F=CNF()
    def eq(l,n):F.extend(CardEnc.equals(l,n,vpool=ids,encoding=EncType.totalizer).clauses)
    for v in roots|set(pins):F.append([x[v]])
    for v in banned:
        if v in x:F.append([-x[v]])
    assert tip in ep;F.append([ep[tip]])
    eq(list(ep.values()),2)
    if c==-1:eq([ep[v] for v in ep if v.bit_count()%2==0],1)
    for k in (0,1):eq([x[v] for v in avail if v.bit_count()%2==k],(target+1)//2+int(c==1-k)-sum(v.bit_count()%2==1-k for v in low))
    for v in avail:
        N=[x[v^1<<j] for j in range(8) if v^1<<j in x];n=2-int(v in roots)
        if v in ep:N.append(ep[v]);F.append([-ep[v],x[v]])
        if len(N)<n:F.append([-x[v]]);continue
        for t in combinations(N,n+1):F.append([-x[v],*[-z for z in t]])
        for t in combinations(N,len(N)-n+1):F.append([-x[v],*t])
        for j,k in combinations(range(8),2):
            square=[v,v^1<<j,v^1<<k,v^1<<j^1<<k]
            if v==min(square) and all(y in x for y in square):F.append([-x[y] for y in square])
    cycles=0;ans=None;found=None
    with Solver(name='cadical195',bootstrap_with=F) as sol:
        if hint:sol.set_phases([x[v] if v in hint else -x[v] for v in avail])
        while True:
            rem=budget-sol.accum_stats()['conflicts']
            if rem<=0:break
            sol.conf_budget(rem);ans=sol.solve_limited()
            if ans!=True:break
            pos=set(sol.get_model());chosen=low|{256+v for v in avail if x[v] in pos};adj={v:{v^1<<j for j in range(9) if v^1<<j in chosen} for v in chosen};ends=[v for v in adj if len(adj[v])==1];assert len(ends)==2
            walk=[ends[0]];visited=set(walk)
            while adj[walk[-1]]-visited:
                v=next(iter(adj[walk[-1]]-visited));walk.append(v);visited.add(v)
            if len(visited)==len(chosen):
                assert len(walk)==target+1
                for j,v in enumerate(walk):
                    for k in range(j):assert ((v^walk[k]).bit_count()==1)==(k+1==j)
                found=walk;break
            cycleset=chosen-visited
            while cycleset:
                start=next(iter(cycleset));queue=[start];component={start}
                while queue:
                    v=queue.pop()
                    for y in adj[v]-component:queue.append(y);component.add(y)
                cycleset-=component;cycles+=1;sol.add_clause([-x[v-256] for v in component if v>=256 and v-256 not in roots])
            ans=None
        conflicts=sol.accum_stats()['conflicts']
    if found:
        with (D/(log+'.paths')).open('a') as f:print(target,i,-1,len(p)-1,len(s)-1,*found,file=f)
    print(json.dumps(dict(id=i,c=c,target=target,answer=ans,conflicts=conflicts,cycles=cycles)),flush=True)
if __name__=='__main__':
    bank=load(D/sys.argv[1]);hint={};dest=sys.argv[4]
    if len(sys.argv)>5:
        for l in (D/sys.argv[5]).read_text().splitlines():
            n,i,seed,p,s,*z=map(int,l.split());hint[i]={v-256 for v in z if v>=256}
    for i,(p,s) in enumerate(bank):
        for c in (0,1):run(p,s,int(sys.argv[2]),c,int(sys.argv[3]),i,dest,hint.get(i))
