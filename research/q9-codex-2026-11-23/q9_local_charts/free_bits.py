"""Conflict-driven repair with unrestricted cube positions outside the pinned time set."""
import itertools
import json
import random
import sys
from pathlib import Path
from pysat.solvers import Solver
from pysat.formula import IDPool

class Cube:
    def __init__(self,n,dim):
        self.dim=dim
        self.s=Solver(name='cadical195')
        self.ids=pool=IDPool()
        self.x=[[pool.id(('x',i,b)) for b in range(dim)] for i in range(n)]
        steps=[[pool.id(('s',i,b)) for b in range(dim)] for i in range(n-1)]
        clause=self.s.add_clause
        for bit in self.x[0]:clause([-bit])
        for i,step in enumerate(steps):
            clause(step)
            for a,b in itertools.combinations(step,2):clause([-a,-b])
            for axis,z in enumerate(step):
                a,b=self.x[i][axis],self.x[i+1][axis]
                for c in ((z,-a,b),(z,a,-b),(-z,a,b),(-z,-a,-b)):clause(c)
                # The same direction cannot recur after zero or one intervening step.
                for j in (i-1,i-2):
                    if j>=0:clause([-z,-steps[j][axis]])
        self.constrained=set()

    def pair(self,i,j):
        assert (i,j) not in self.constrained
        self.constrained.add((i,j))
        differs=[]
        for k,(a,b) in enumerate(zip(self.x[i],self.x[j])):
            d=self.ids.id(('diff',i,j,k))
            self.s.add_clause([-d,a,b]);self.s.add_clause([-d,-a,-b]);differs.append(d)
        if (j-i)%2:
            # Every possible singleton difference is forbidden.
            for k in range(self.dim):self.s.add_clause(differs[:k]+differs[k+1:])
        else:self.s.add_clause(differs)

    def pins(self,p):
        bits=[];sels=[]
        for i,(row,v) in enumerate(zip(self.x,p)):
            wanted=[a if v>>b&1 else -a for b,a in enumerate(row)]
            z=self.ids.id(('pin',i,v))
            for lit in wanted:self.s.add_clause([-z,lit])
            bits+=wanted;sels.append(z)
        self.s.set_phases(bits)
        return sels

    def query(self,pins,limit,rounds):
        for _ in range(rounds):
            self.s.conf_budget(limit)
            ans=self.s.solve_limited(assumptions=pins)
            if ans is not True:
                return ('limit',None) if ans is None else ('unsat',self.s.get_core() or [])
            model=set(self.s.get_model())
            p=[sum(1<<b for b,a in enumerate(row) if a in model) for row in self.x]
            bad=[(i,j) for j,v in enumerate(p) for i in range(j-1) if (p[i]^v).bit_count()<=1]
            if not bad:
                assert p[0]==0 and all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
                return 'hit',p
            for i,j in bad:self.pair(i,j)
        return 'round_limit',None

def readbank(f):
    return [list(map(int,s.split())) for s in Path(f).read_text().splitlines() if s.strip()]

def run(seed,runs,mode,f):
    rng=random.Random(seed);bank=readbank(f)
    for trial in range(runs):
        row=rng.randrange(len(bank));p=bank[row][::rng.choice((1,-1))]
        p=[v^p[0] for v in p]
        if mode=='reference':
            dim=3
            p=[0];n=rng.randint(4,8)
            for i in range(n-1):p.append(p[-1]^1<<rng.randrange(dim))
            locked={i for i in range(n) if rng.random()<.55}
            def exact(w):
                i=len(w)
                if i==len(p):return True
                for b in range(dim):
                    x=w[-1]^(1<<b)
                    if i in locked and x!=p[i]:continue
                    if x in w or any((x^y).bit_count()<=1 for y in w[:-1]):continue
                    if exact(w+[x]):return True
                return False
            c=Cube(n,dim);selectors=c.pins(p)
            status,val=c.query([selectors[i] for i in locked],20000,100)
            assert status in ('hit','unsat') and (status=='hit')==exact([0])
            c.s.delete()
            print(json.dumps(dict(trial=trial,status=status)),flush=True)
            continue
        if mode=='plant':
            k=next(j for j in range(len(p)-51) if all((p[a]^p[b]).bit_count()>1 for b in range(j,j+51) for a in range(j,b-1)))
            p=p[k:k+51];p=[v^p[0] for v in p]
            at=rng.randrange(2,len(p)-2);p[at]^=3
        c=Cube(len(p),9)
        selectors=c.pins(p);index={v:i for i,v in enumerate(selectors)}
        locked=set(range(1,len(p)))
        if mode!='plant':
            # Initial release near the endpoints of each defect plus scattered short windows.
            for j,x in enumerate(p):
                for i in range(j-1):
                    if (x^p[i]).bit_count()<=1:
                        for k in (i,j):
                            if rng.random()<.78:
                                w=rng.randint(2,12);locked.difference_update(range(k-w,k+w+1))
            for _ in range(2+trial%5):
                k=rng.randrange(len(p));locked.difference_update(range(k,k+rng.randint(2,10)))
        history=[];sol=None
        for step in range(50):
            pins=[selectors[i] for i in sorted(locked)]
            status,data=c.query(pins,3000 if mode=='plant' else 2500,100 if mode=='plant' else 22)
            history.append([status,len(locked),len(c.constrained)])
            if status=='hit':sol=data;break
            if status=='unsat':
                candidates=[index[x] for x in data]
                if not candidates:break
                focus=rng.choice(candidates)
            else:
                if mode=='plant':break
                if not locked:break
                # Once a given partially pinned instance times out, reserve the rest of the budget
                # for other roots rather than repeatedly relaxing into the same difficult instance.
                if sum(h[0] in ('limit','round_limit') for h in history)>=3:break
                focus=rng.choice(sorted(locked))
            radius=rng.randint(1,6) if mode!='plant' else 1
            locked.difference_update(range(focus-radius,focus+radius+1))
        c.s.delete()
        print(json.dumps(dict(trial=trial,row=row,history=history,vertices=sol),separators=(',',':')),flush=True)
        if sol and mode=='target':break
if __name__=='__main__':
    run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3],sys.argv[4])
