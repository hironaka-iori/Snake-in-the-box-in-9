from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
import json,sys,random
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
D=Path(__file__).resolve().parent
rows=[list(map(int,line.split())) for line in (D/'seeds.dat').read_text().splitlines()];source=[z[2:2+z[1]] for z in rows];N=[{v^1<<j for j in range(8)} for v in range(256)]
seed=int(sys.argv[1]);L=int(sys.argv[2]);limit=int(sys.argv[3]);cap=int(sys.argv[4]);dest=sys.argv[5];p=source[seed];pos={v:i for i,v in enumerate(p)};rng=random.Random(635+seed+L)
cand=[]
for x in range(256):
    for a,b,c in permutations(range(8),3):
        q=[x,x^1<<a,x^1<<a^1<<b,x^1<<a^1<<b^1<<c]
        if x>q[-1]:continue
        bad=set.union(*(N[v]|{v} for v in q));ix=[i for i,v in enumerate(p) if v in bad]
        blocks=[(j+1,k-1) for j,k in zip([-1,*ix],[*ix,len(p)]) if k-j-1>=24]
        if not blocks:continue
        lo,hi=max(blocks,key=lambda z:z[1]-z[0])
        cand.append((len(ix)+rng.random()*6,lo,hi,q,bad))
cand.sort(key=lambda x:x[0])
found=0
for count,(rank,lo,hi,s,bad) in enumerate(cand[:cap]):
    if hi-lo>39:
        start=rng.randrange(lo,hi-39+1);lo,hi=start,start+39
    fixed=set(p[lo:hi+1]);allow=set(range(256))-bad
    for v in p[lo+1:hi]:allow-=N[v]-fixed
    allow=sorted(allow);pool=IDPool();X={v:pool.id(('x',v)) for v in allow};E={v:pool.id(('e',v)) for v in allow if v not in fixed-{p[lo],p[hi]}};F=CNF()
    def eq(ls,k):
        if not 0<=k<=len(ls):F.append([]);return
        F.extend(CardEnc.equals(ls,k,vpool=pool,encoding=EncType.totalizer).clauses)
    for v in fixed:F.append([X[v]])
    eq(list(E.values()),2)
    for v in allow:
        z=[X[n] for n in sorted(N[v]&X.keys())]
        if v in E:z.append(E[v]);F.append([-E[v],X[v]])
        for t in combinations(z,3):F.append([-X[v],*[-a for a in t]])
        if len(z)<2:F.append([-X[v]])
        else:
            for t in combinations(z,len(z)-1):F.append([-X[v],*t])
        for a,b in combinations(range(8),2):
            cell=(v,v^1<<a,v^1<<b,v^1<<a^1<<b)
            if v==min(cell) and all(y in X for y in cell):F.append([-X[y] for y in cell])
    # Alternate colours of the pair when L is even, either colour is possible.
    color=count%2
    for col in (0,1):
        picked=[v for v in allow if v.bit_count()%2==col];eq([X[v] for v in picked if v not in fixed],(L+1)//2+int(L%2==0 and color==col)-sum(v in fixed for v in picked))
        eq([e for v,e in E.items() if v.bit_count()%2==col],1 if L%2 else 2*int(color==col))
    with Solver(name='cadical195',bootstrap_with=F) as solver:
        solver.set_phases([X[v] if v in pos else -X[v] for v in X]);cycles=0
        while True:
            rem=limit-solver.accum_stats()['conflicts']
            if rem<=0:answer=None;break
            solver.conf_budget(rem);answer=solver.solve_limited()
            if answer!=True:break
            md=set(solver.get_model());chosen={v for v in X if X[v] in md};ends=[v for v in chosen if len(N[v]&chosen)==1];assert len(ends)==2
            walk=[ends[0]];seen=set(walk)
            while (N[walk[-1]]&chosen)-seen:
                v=next(iter((N[walk[-1]]&chosen)-seen));walk.append(v);seen.add(v)
            if len(seen)==len(chosen):
                with (D/(dest+'.dat')).open('a') as out:print(seed,0,lo,hi,len(walk),*walk,len(s),*s,file=out)
                found+=1;break
            while chosen-seen:
                todo=[next(iter(chosen-seen))];comp=set(todo)
                while todo:
                    v=todo.pop()
                    for n in (N[v]&chosen)-comp:comp.add(n);todo.append(n)
                seen|=comp;cycles+=1;solver.add_clause([-X[v] for v in comp])
        if answer==True:print('found',count,L,seed,lo,hi,flush=True)
    if found>=8:break
print('tested',count+1,'found',found,flush=True)
