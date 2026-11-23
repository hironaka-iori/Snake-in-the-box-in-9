from pathlib import Path
import sys,json,os,time
from itertools import combinations
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
D=Path(__file__).resolve().parent
def nbs(v):return {v^1<<j for j in range(9)}
def search(src,id,low,short,anchor,initial,target,c,cap,log,m):
    start=time.monotonic()
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
    # A 92-edge main path has 47 projected vertices of its endpoint colour and 46 of the other.
    for h in (0,1):
        lowcount=L//2+int(m==h)+sum(v.bit_count()%2==h for v in short)
        for layer in (0,1):
            required=lowcount if not layer else target//2+int(c==h)-lowcount
            vertices=[v for v in avail if (v>=256)==bool(layer) and v.bit_count()%2==h]
            eq([X[v] for v in vertices if v not in yes],required-sum(v in yes for v in vertices))
        crossh=[pool.id(('cross',v)) for v in avail if v<256 and v+256 in X and v not in short and v.bit_count()%2==h]
        eq(crossh,2*int(h==m))
    # Each of the four antipodal pairs in a Q3 leaves an induced six-cycle in its complement.
    for axes in combinations(range(9),3):
        shifts=[0]
        for j in axes:shifts+=[z^1<<j for z in shifts]
        mask=shifts[-1]
        for b in range(512):
            if b&mask:continue
            cube={b^z for z in shifts}
            for z in shifts[:4]:
                cycle=cube-{b^z,b^z^mask}
                if cycle<=X.keys():F.append([-X[v] for v in sorted(cycle-yes)])
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
    with Solver(name='cadical195',bootstrap_with=F,with_proof=bool(os.getenv('EXPORT'))) as sol:
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
        if os.getenv('EXPORT') and ans is False:
            assert cuts==0
            tag=D/f'case{src}_target{target}_c{c}m{m}';F.to_file(str(tag)+'.cnf');Path(str(tag)+'.drat').write_text('\n'.join(sol.get_proof())+'\n')
        n=sol.accum_stats()['conflicts']
    if path:
        for j,v in enumerate(path):
            for i in range(j):assert ((v^path[i]).bit_count()==1)==(i+1==j)
        with (D/(log+'.paths')).open('a') as f:print(target,id,src,L,k,*path,file=f)
    print(json.dumps(dict(seed=src,id=id,lower_end_color=m,seconds=round(time.monotonic()-start,2),anchor_edges=len(anchor)-1,target=target,c=c,budget=cap,outcome=ans,cycles=cuts,conflicts=n)),flush=True)

if __name__=='__main__':
    cases=json.loads((D/'cases.json').read_text());idx=int(sys.argv[1]);r=cases[idx];target=int(sys.argv[2]);budget=int(sys.argv[3]);log=sys.argv[4]
    branches=[(int(v[0]),int(v[1])) for v in sys.argv[5:]]
    for c,m in branches:search(r['source'],r['row'],[0]*(r['L']+1),r['short'],r['anchor'],set(r['hint']),target,c,budget,log,m)
