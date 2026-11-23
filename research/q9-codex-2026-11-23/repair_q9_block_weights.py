"""Find an induced Q9 path preserving signed per-block Hamming weights in time."""
import itertools
import json
from pathlib import Path
import random
import sys
from pysat.solvers import Solver
from repair_q9_time_projection import valid

def repair(path, groups, budget):
    masks=[sum(1<<a for a in g) for g in groups]
    sizes=[len(g) for g in groups]
    symbols=[]
    previous=[None]*len(groups)
    active=[None]*len(groups)
    first=[True]*len(groups)
    clauses=[]
    hints=[]
    nextvar=1
    def equality(u,v):
        nonlocal nextvar
        if u==v:return True
        k=(min(u,v),max(u,v))
        if k not in eqcache:
            z=nextvar
            nextvar+=1
            eqcache[k]=z
            for a,b in zip(u,v):
                clauses.extend(([-a,-b,z],[-a,b,-z]))
        return eqcache[k]
    eqcache={}
    for x in path:
        weights=tuple((x&m).bit_count() for m in masks)
        for j,(g,m,n,w) in enumerate(zip(groups,masks,sizes,weights)):
            if w==previous[j]:continue
            previous[j]=w
            if w in (0,n):
                active[j]=None
                continue
            active[j]=u=tuple(range(nextvar,nextvar+n))
            nextvar+=n
            clauses.append(list(u))
            clauses.extend([-a,-b] for a,b in itertools.combinations(u,2))
            wanted=x&m if w==1 else ~x&m
            h=u[next(k for k,a in enumerate(g) if wanted&(1<<a))]
            hints.append(h)
            if first[j]:
                clauses.append([h])
                first[j]=False
        symbols.append((weights,tuple(active)))
    def excess(i,j):
        w,us=symbols[i]
        v,vs=symbols[j]
        lits=[]
        for a,b,u,s in zip(w,v,us,vs):
            if u is None or s is None:continue
            z=equality(u,s)
            if z is True:
                if a!=b:return True,[]
            else:lits.append(z if a!=b else -z)
        return False,lits
    seen={}
    for i,(ws,us) in enumerate(symbols):
        if i:
            always,lits=excess(i-1,i)
            assert not always
            clauses.extend([-z] for z in lits)
        neighbors=[ws]
        for k,length in enumerate(sizes):
            for e in (-1,1):
                if 0<=ws[k]+e<=length:
                    neighbors.append(ws[:k]+(ws[k]+e,)+ws[k+1:])
        for t in neighbors:
            for j in seen.get(t,()):
                if j+1==i:continue
                always,lits=excess(j,i)
                if not always:
                    if not lits:return 'UNSAT',None
                    clauses.append(lits)
        seen.setdefault(ws,[]).append(i)
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        solver.set_phases(hints)
        solver.conf_budget(budget)
        result=solver.solve_limited()
        if result is not True:return ('UNKNOWN' if result is None else 'UNSAT'),None
        model=set(solver.get_model())
    out=[]
    for ws,us in symbols:
        x=0
        for g,m,n,w,u in zip(groups,masks,sizes,ws,us):
            if w==0:continue
            if w==n:x|=m
            else:
                bit=next(a for a,b in zip(g,u) if b in model)
                x|=1<<bit if w==1 else m^(1<<bit)
        out.append(x)
    assert valid(out)
    return 'FOUND',out

if __name__=='__main__':
    file,shape,count,budget,seed=sys.argv[1:6]
    path=Path(file)
    if file.endswith('.json'):bank=[json.loads(path.read_text())['vertices']]
    elif file.endswith('.log'):bank=[list(map(int,l.split(' sample ')[1].split())) for l in path.read_text().splitlines() if l.startswith('MIN ')]
    else:bank=[list(map(int,l.split())) for l in path.read_text().splitlines() if l.strip()]
    sizes=list(map(int,shape))
    assert sum(sizes)==9 and set(sizes)<={1,2,3}
    r=random.Random(int(seed))
    for trial in range(int(count)):
        n=r.randrange(len(bank))
        axes=list(range(9))
        r.shuffle(axes)
        groups=[]
        for s in sizes:
            groups.append(sorted(axes[:s]))
            axes=axes[s:]
        shift=r.randrange(512)
        state,w=repair([x^shift for x in bank[n]],groups,int(budget))
        print(json.dumps([n,groups,shift,state,w],separators=(',',':')),flush=True)
        if w:break
