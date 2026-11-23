"""Lift an entire sequence of coordinate-block parities back to an induced Q9 path."""
import itertools,json,random,sys
from pathlib import Path
from pysat.solvers import Solver
from repair_q9_time_projection import valid

def build(path,groups,rng,free,exception=None):
    bad={t for i,x in enumerate(path) for j in range(i+2,len(path)) if (x^path[j]).bit_count()<2 for t in (i,j)}
    syms=[[] for _ in path]
    parity=[0]*len(path)
    nextvar=1
    clauses=[]
    hints=[]
    tables=[]
    choices={}
    for k,g in enumerate(groups):
        n=len(g)
        lookup={}
        for b in range(1<<n):
            par=b.bit_count()%2
            lab=min(b,b^7) if n==3 else (b&1 if n==2 else 0)
            lookup[par,lab]=sum(1<<a for j,a in enumerate(g) if b&(1<<j))
        tables.append(lookup)
        start=0
        for end in range(1,len(path)+1):
            if end<len(path) and all(not ((path[end]^path[end-1])&(1<<a)) for a in g):continue
            x=path[start]
            raw=sum((1<<j) for j,a in enumerate(g) if x&(1<<a))
            par=raw.bit_count()%2
            value=min(raw,raw^7) if n==3 else (raw&1 if n==2 else 0)
            dom=1<<(n-1)
            if dom>1 and (rng.random()<free or any(start<=t<end for t in bad)) and start!=0:
                u=tuple(range(nextvar,nextvar+dom))
                nextvar+=dom
                hints.append(u[value]);clauses.append(list(u))
                clauses.extend([-a,-b] for a,b in itertools.combinations(u,2))
            else:u=value
            for i in range(start,end):
                syms[i].append(u)
                parity[i]|=par<<k
            start=end
    eqcache={}
    def equality(a,b):
        nonlocal nextvar
        if a==b:return True
        if isinstance(a,int):
            return False if isinstance(b,int) else b[a]
        if isinstance(b,int):return a[b]
        key=(min(a,b),max(a,b))
        z=eqcache.get(key)
        if z is None:
            z=nextvar;nextvar+=1
            eqcache[key]=z
            for x,y in zip(a,b):clauses.extend(([-x,-y,z],[-x,y,-z]))
        return z
    seen={}
    for i,(mask,row) in enumerate(zip(parity,syms)):
        if i:
            k=(mask^parity[i-1]).bit_length()-1
            if len(groups[k])==3:
                e=equality(row[k],syms[i-1][k])
                if e is True:return None
                if e is not False:clauses.append([-e])
        for d in [-1,*range(len(groups))]:
            other=mask if d<0 else mask^(1<<d)
            for j in seen.get(other,()):
                if j==i-1 or exception==(j,i):continue
                lits=[]
                for k,(u,v) in enumerate(zip(row,syms[j])):
                    if k==d and len(groups[k])!=3:continue
                    z=equality(u,v)
                    if (z is True and k==d) or (z is False and k!=d):break
                    if type(z) is int:lits.append(z if k==d else -z)
                else:
                    if not lits:return None
                    clauses.append(lits)
        seen.setdefault(mask,[]).append(i)
    return clauses,hints,syms,parity,tables

def solve(path,groups,rng,free,budget):
    inst=build(path,groups,rng,free)
    if inst is None:return 'UNSAT',None
    clauses,hints,rows,parities,tables=inst
    with Solver(name='cadical195',bootstrap_with=clauses) as solver:
        solver.set_phases(hints);solver.conf_budget(budget)
        ans=solver.solve_limited()
        if ans is not True:return ('UNKNOWN' if ans is None else 'UNSAT'),None
        positive=set(solver.get_model())
    out=[]
    for row,p in zip(rows,parities):
        coords=0
        for k,v in enumerate(row):
            value=v if isinstance(v,int) else next(j for j,b in enumerate(v) if b in positive)
            coords|=tables[k][(p>>k)&1,value]
        out.append(coords)
    assert valid(out)
    return 'FOUND',out

if __name__=='__main__':
    file,form,count,budget,seed=sys.argv[1:6]
    if file.endswith('.json'):bank=[json.loads(Path(file).read_text())['vertices']]
    elif file.endswith('.log'):bank=[list(map(int,l.split(' sample ')[1].split())) for l in Path(file).read_text().splitlines() if l.startswith('MIN ')]
    else:bank=[list(map(int,l.split())) for l in Path(file).read_text().splitlines() if l]
    rng=random.Random(int(seed)); sizes=list(map(int,form))
    assert sum(sizes)==9 and min(sizes)>=1 and max(sizes)<=3
    for t in range(int(count)):
        n=rng.randrange(len(bank));dims=list(range(9));rng.shuffle(dims);groups=[]
        for size in sizes:
            groups.append(sorted(dims[:size]));dims=dims[size:]
        free=rng.choice([.25,.40,.55,.7,.8,.95]) if len(sys.argv)<=6 else float(sys.argv[6])
        status,w=solve(bank[n],groups,rng,free,int(budget))
        print(json.dumps([t,n,groups,free,status,w],separators=(',',':')),flush=True)
        if w:break
