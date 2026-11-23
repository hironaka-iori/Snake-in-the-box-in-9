"""Encode a fixed timetable in Q9, with time-dependent vertex domains."""
import itertools
import json
import random
import sys
from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def valid(p):
    return len(set(p))==len(p) and all(0<=x<512 for x in p) and all(((x^p[j]).bit_count()==1)==(j+1==i) for i,x in enumerate(p) for j in range(i))

def csp(rows,seed,budget):
    pool=IDPool()
    cells=[{x:pool.id((i,x)) for x in domain} for i,domain in enumerate(rows)]
    used={x:[] for d in cells for x in d}
    clauses=[]
    def amo(xs):
        if len(xs)>1:
            clauses.extend(CardEnc.atmost(xs,1,vpool=pool,encoding=EncType.seqcounter).clauses)
    for d in cells:
        clauses.append(list(d.values()))
        amo(list(d.values()))
        for x,k in d.items():used[x].append(k)
    on={x:pool.id(('on',x)) for x in used}
    for x,ls in used.items():
        amo(ls)
        clauses.extend([-k,on[x]] for k in ls)
    for i,row in enumerate(cells):
        prev=cells[i-1] if i else {}
        nex=cells[i+1] if i+1<len(cells) else {}
        for x,k in row.items():
            hood=[x^(1<<b) for b in range(9)]
            if nex:clauses.append([-k]+[nex[y] for y in hood if y in nex])
            for y in hood:
                if y in used:
                    clauses.append([-k,-on[y]]+([prev[y]] if y in prev else [])+([nex[y]] if y in nex else []))
    with Solver(name='cadical195',bootstrap_with=clauses) as sat:
        sat.set_phases([r[x] for r,x in zip(cells,seed) if x in r])
        sat.conf_budget(budget)
        status=sat.solve_limited()
        if status:
            data=set(sat.get_model());p=[next(x for x,k in row.items() if k in data) for row in cells]
            assert valid(p)
        else:p=None
        return status,p,sat.accum_stats()['conflicts']

def make(seed,axes,rng,style):
    # Give every time position the parity of the starting template at that position.
    dsets=[];old=set()
    i=0
    while i<len(seed):
        size=rng.randint(4,30)
        pinned=set(rng.sample(sorted(old),max(0,axes-2))) if old and style%3==1 else set()
        extra=rng.sample(sorted(set(range(9))-pinned),axes-len(pinned))
        old=pinned|set(extra)
        masks=[sum(1<<b for b in subset) for j in range(0,axes+1,2) for subset in itertools.combinations(old,j)]
        dsets.extend([[x^m for m in masks] for x in seed[i:i+size]])
        i+=size
    return dsets

def main():
    rand,n,axes,limit,mode,infile=sys.argv[1:]
    rng=random.Random(int(rand));bank=[list(map(int,l.split())) for l in Path(infile).read_text().splitlines() if l.strip()]
    for i in range(int(n)):
        idx=rng.randrange(len(bank));p=bank[idx][::rng.choice((1,-1))]
        if mode=='short':
            p=[rng.randrange(16) for _ in range(rng.randint(3,6))]
            rows=[]
            for k,x in enumerate(p):
                d=rng.sample(range(16),rng.randrange(1,5))
                rows.append(d)
            exact=any(valid(t) for t in itertools.product(*rows))
        else:
            assert all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
            if mode=='plant':
                p=next(p[j:j+57] for j in range(len(p)-56) if valid(p[j:j+57]))
            rows=make(p,int(axes),rng,i)
            if mode=='plant':
                p=[(r[1] if j%7==4 else r[0]) for j,r in enumerate(rows)]
                assert not valid(p)
        status,sol,conf=csp(rows,p,int(limit))
        if mode=='short':assert status==exact
        if mode=='plant':assert status is not False
        print(json.dumps(dict(i=i,row=idx,outcome=('hit' if status else 'limit' if status is None else 'unsat'),conflicts=conf,vertices=sol)),flush=True)
        if sol and mode=='target':break

if __name__=='__main__':main()
