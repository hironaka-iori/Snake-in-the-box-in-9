from itertools import combinations
from pathlib import Path
from pysat.solvers import Solver
from repair_q9_time_projection import valid
import json,sys,random

def matchings(axes,count):
    if not count:
        yield ()
        return
    if len(axes)<2*count:return
    a,*rest=axes
    yield from matchings(rest,count)
    for i,b in enumerate(rest):
        for tail in matchings(rest[:i]+rest[i+1:],count-1):yield ((a,b),)+tail

def repair(p,pairs,budget):
    """Preserve every pair's weight at each time, freely choose all orientations."""
    keep=511
    for a,b in pairs:keep^=(1<<a)|(1<<b)
    baseline=[v&keep for v in p]
    runs=[[] for _ in p]
    hints=[];clauses=[];last=0
    for a,b in pairs:
        mask=(1<<a)|(1<<b);prev=-1;first=True
        for i,v in enumerate(p):
            w=(v&mask).bit_count()
            if w==1:
                if prev!=1:
                    last+=1
                    hints.append(last if v&(1<<a) else -last)
                    if first:clauses.append([hints[-1]]);first=False
                runs[i].append(last);baseline[i]|=1<<a
            else:
                runs[i].append(0)
                if w==2:baseline[i]|=mask
            prev=w
    aux={};seen=set()
    for i,x in enumerate(baseline):
        for j in range(i+2,len(p)):
            if (x^baseline[j]).bit_count()>=2:continue
            lits=[]
            for u,v in zip(runs[i],runs[j]):
                if u==v or not u or not v:continue
                if (u,v) not in aux:
                    last+=1;aux[u,v]=last
                    clauses.extend(([-last,u,v],[-last,-u,-v],[last,-u,v],[last,u,-v]))
                lits.append(aux[u,v])
            if not lits:return 'UNSAT',None
            key=tuple(lits)
            if key not in seen:seen.add(key);clauses.append(lits)
    with Solver(name='cadical195',bootstrap_with=clauses) as sat:
        sat.set_phases(hints);sat.conf_budget(budget)
        outcome=sat.solve_limited()
        if outcome is not True:return ('UNKNOWN' if outcome is None else 'UNSAT'),None
        model=set(sat.get_model())
    path=baseline[:]
    for i,r in enumerate(runs):
        for (a,b),var in zip(pairs,r):
            if var and var not in model:path[i]^=(1<<a)|(1<<b)
    assert valid(path)
    return 'FOUND',path

if __name__=='__main__':
    name,count,budget=sys.argv[1:4];lines=Path(name).read_text().splitlines()
    if name.endswith('.log'):bank=[list(map(int,l.split(' sample ')[1].split())) for l in lines if l.startswith('MIN ')]
    elif name.endswith('.json'):bank=[json.loads(''.join(lines))['vertices']]
    else:bank=[list(map(int,l.split())) for l in lines if l.strip()]
    choices=list(matchings(tuple(range(9)),4));assert len(choices)==945
    tasks=list(range(len(choices)*len(bank)));random.Random(459210).shuffle(tasks)
    for t in tasks[:int(count)]:
        n,m=divmod(t,len(choices));st,w=repair(bank[n],choices[m],int(budget))
        print(json.dumps([st,n,choices[m],w],separators=(',',':')),flush=True)
        if w:break
