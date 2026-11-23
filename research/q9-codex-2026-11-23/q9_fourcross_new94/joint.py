from pathlib import Path
import sys,json
from itertools import combinations
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
D=Path(__file__).resolve().parent
def nbs(v):return {v^1<<j for j in range(9)}
def search(src,id,low,short,anchor,initial,target,c,cap,log):
    L=len(low)-1;k=len(short)-1;yes=set(anchor+short)|{256+short[0],256+short[-1]};no=set()
    for v in short:no|={q for q in nbs(v) if q<256 and q not in short}
    for v in yes:
        if len(nbs(v)&yes)==2:no|=nbs(v)-yes
    assert not no&yes
    pool=IDPool();avail=sorted(set(range(512))-no);X={v:pool.id(('x',v)) for v in avail};high=lambda v:v.bit_count()%2
    ep={v:pool.id(('end',v)) for v in avail if v>=256 and high(v)==c};F=CNF()
    def eq(l,n):
        if not 0<=n<=len(l):F.append([]);return
        F.extend(CardEnc.equals(l,n,vpool=pool,encoding=EncType.totalizer).clauses)
    for v in yes:F.append([X[v]])
    eq(list(ep.values()),2)
    eq([X[v] for v in avail if v<256 and v not in yes],L+1+len(short)-sum(v<256 for v in yes))
    for h in (0,1):eq([X[v] for v in avail if v not in yes and high(v)==h],target//2+int(c==h)-sum(high(v)==h for v in yes))
    crosses=[]
    for v in avail:
        if v<256 and v+256 in X and v not in short:
            z=pool.id(('cross',v));F.extend([[-z,X[v]],[-z,X[v+256]],[z,-X[v],-X[v+256]]]);crosses.append(z)
    eq(crosses,2)
    for v in avail:
        nb=nbs(v);need=2-len(nb&yes);z=[X[q] for q in sorted(nb-yes) if q in X]
        if v in ep:z.append(ep[v]);F.append([-ep[v],X[v]])
        if not 0<=need<=len(z):F.append([-X[v]]);continue
        for t in combinations(z,need+1):F.append([-X[v],*[-j for j in t]])
        for t in combinations(z,len(z)-need+1):F.append([-X[v],*t])
        for a,b in combinations(range(9),2):
            q={v,v^1<<a,v^1<<b,v^1<<a^1<<b}
            if v==min(q) and q<=X.keys():F.append([-X[j] for j in q-yes])
    cuts=0;ans=None;path=None
    with Solver(name='cadical195',bootstrap_with=F) as sol:
        sol.set_phases([X[v] if v in initial else -X[v] for v in avail])
        while True:
            left=cap-sol.accum_stats()['conflicts']
            if left<=0:break
            sol.conf_budget(left);ans=sol.solve_limited()
            if ans!=True:break
            md=set(sol.get_model());occ={v for v in X if X[v] in md};N={v:nbs(v)&occ for v in occ};ends=[v for v in occ if len(N[v])==1];assert len(ends)==2
            walk=[ends[0]];seen=set(walk)
            while N[walk[-1]]-seen:
                v=next(iter(N[walk[-1]]-seen));walk.append(v);seen.add(v)
            if seen==occ:
                path=walk;assert len(walk)==target+1 and sum((u^v)==256 for u,v in zip(walk,walk[1:]))==4;break
            while occ-seen:
                block={next(iter(occ-seen))};todo=list(block)
                while todo:
                    v=todo.pop()
                    for q in N[v]-block:block.add(q);todo.append(q)
                seen|=block;sol.add_clause([-X[v] for v in block-yes]);cuts+=1
            ans=None
        n=sol.accum_stats()['conflicts']
    if path:
        for j,v in enumerate(path):
            for i in range(j):assert ((v^path[i]).bit_count()==1)==(i+1==j)
        with (D/(log+'.paths')).open('a') as f:print(target,id,src,L,k,*path,file=f)
    print(json.dumps(dict(seed=src,id=id,anchor_edges=len(anchor)-1,target=target,c=c,budget=cap,outcome=ans,cycles=cuts,conflicts=n)),flush=True)
def run(r,file,trace,source,target,budget,log):
    bank=[list(map(int,z.split())) for z in (D/file).read_text().splitlines()];w=[list(map(int,t.split())) for t in (D/trace).read_text().splitlines()];w=[z for z in w if z[1]==r];org=list(map(int,(D/'seeds.dat').read_text().splitlines()[source].split()));orig=org[2:2+org[1]]
    seed,rev,lo,hi,n,*z=bank[r];p=z[:n];s=z[n+1:];orig=orig[::-1] if rev else orig;anchor=orig[lo:hi+1];assert any(v==anchor or v==anchor[::-1] for v in (p[i:i+len(anchor)] for i in range(len(p)-len(anchor)+1)))
    hint=set(w[-1][5:]) if w else set(p+s)
    for c in (0,1):search(source,r,p,s,anchor,hint,target,c,budget,log)
if __name__=='__main__':
    goal=int(sys.argv[1]);budget=int(sys.argv[2]);name=sys.argv[3]
    for args in [(1,'freer92.dat','free184.paths',1),(5,'freer92.dat','free184.paths',1),(1,'spliced.dat','linked0.paths',0)]:
        run(*args,goal,budget,name)
