"""Fix the projection at each time and freely reconstruct d hidden coordinate bits."""
from itertools import combinations
from pathlib import Path
from pysat.solvers import Solver
import json, random, sys

def valid(p):
    return all(0 <= v < 512 for v in p) and len(set(p))==len(p) and all(((v^p[j]).bit_count()==1)==(j==i+1) for i,v in enumerate(p) for j in range(i+1,len(p)))

def repair(p,axes,budget, excluded=()):
    mask=sum(1<<a for a in axes)
    vis=[v&~mask for v in p]
    g=[0]
    for a,b in zip(vis,vis[1:]):
        g.append(g[-1]+int(a==b))
    d=len(axes)
    groups=g[-1]+1
    dom=[{v: k*(1<<(d-1))+j+1 for j,v in enumerate(v for v in range(1<<d) if v.bit_count()%2==k%2)} for k in range(groups)]
    clauses=[[dom[0][0]]]
    if groups>1:
        clauses.append([dom[1][1]])
    for row in dom:
        clauses.append(list(row.values()))
        clauses.extend([-a,-b] for a,b in combinations(row.values(),2))
    allowed={(k,k+1):2 for k in range(groups-1)}
    for i,a in enumerate(vis):
        for j in range(i+2,len(vis)):
            delta=(a^vis[j]).bit_count()
            if delta<=1:
                k,h=g[i],g[j]
                if k==h:
                    return 'UNSAT',None
                allowed[k,h]=allowed.get((k,h),(1<<(d+1))-1) & ~((1<<(2-delta))-1)
    for labels in excluded:
        assert len(labels)==groups and labels[0]==0
        clauses.append([-dom[k][v] for k,v in enumerate(labels)])
    forbids={}
    for (k,h),bits in allowed.items():
        key=(k%2,h%2,bits)
        if key not in forbids:
            forbids[key]=[(a,b) for a in dom[k] for b in dom[h] if not bits&(1<<(a^b).bit_count())]
        clauses.extend([-dom[k][a],-dom[h][b]] for a,b in forbids[key])
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        solver.conf_budget(budget)
        status=solver.solve_limited()
        if status is not True:
            return ('UNKNOWN' if status is None else 'UNSAT'),None
        model=set(solver.get_model())
    values=[next(a for a,v in row.items() if v in model) for row in dom]
    w=[v|sum(((values[k]>>j)&1)<<ax for j,ax in enumerate(axes)) for v,k in zip(vis,g)]
    assert valid(w)
    return 'FOUND',w

def key(seq):
    m={0:0}
    return bytes(m.setdefault(a,len(m)) for a in seq)

if __name__=='__main__':
    source,d,limit,budget=sys.argv[1:]
    bank=[list(map(int,l.split())) for l in Path(source).read_text().splitlines() if l.strip()]
    axes=list(combinations(range(9),int(d)))
    tasks=list(range(len(axes)*len(bank)))
    random.Random(99).shuffle(tasks)
    done=set()
    for t in tasks:
        n,r=divmod(t,len(axes))
        p=bank[n]
        mask=sum(1<<a for a in axes[r])
        word=[(a^b)&~mask for a,b in zip(p,p[1:])]
        canonical=min(key(word),key(reversed(word)))
        if canonical in done:continue
        done.add(canonical)
        status,w=repair(p,axes[r],int(budget))
        print(json.dumps([status,n,axes[r],w],separators=(',',':')),flush=True)
        if w or len(done)>=int(limit):break
