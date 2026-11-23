"""Find a Q9 induced path with each time index allowed its own list of vertices."""
import argparse
import json
import random
from verify_q9_record_facet_profile import canonical
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

NB = [[x^(1<<b) for b in range(9)] for x in range(512)]
MASK = [(1<<i)^(1<<j) for i,j in combinations(range(9),2)]

def check(p):
    return (len(set(p)) == len(p) and all(0<=x<512 for x in p) and
            all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p))))

def solve(seed,rng,width,budget,freeze,repair_sites=None,blacklist=None):
    n=len(seed)
    masks=[0,*rng.sample(MASK,width)]
    domains=[]
    for i,x in enumerate(seed):
        if (repair_sites is not None and i not in repair_sites) or (repair_sites is None and rng.random()<freeze):
            domains.append({x})
            continue
        opts=set(masks)
        for j in (i-2,i-1,i):
            if 0<=j<n-2:opts.add(seed[j]^seed[j+2])
        domains.append({x^m for m in opts})
    return solve_domains(seed,domains,budget,blacklist)

def solve_domains(seed,domains,budget,blacklist=None):
    n=len(seed)
    pool=IDPool(start_from=513)
    ids=[{v:pool.id((i,v)) for v in sorted(D)} for i,D in enumerate(domains)]
    occ=[[] for _ in range(512)]
    cnf=[]
    def atmostone(lits):
        if len(lits)<2:return
        if len(lits)<=6:cnf.extend([-a,-b] for a,b in combinations(lits,2))
        else:cnf.extend(CardEnc.atmost(lits,bound=1,vpool=pool,encoding=EncType.seqcounter).clauses)
    for i,D in enumerate(ids):
        lits=list(D.values());cnf.append(lits);atmostone(lits)
        prev=ids[i-1] if i else {}
        nxt=ids[i+1] if i+1<n else {}
        for v,var in D.items():
            occ[v].append(var);cnf.append([-var,v+1])
            if nxt:cnf.append([-var,*[nxt[w] for w in NB[v] if w in nxt]])
            if prev:cnf.append([-var,*[prev[w] for w in NB[v] if w in prev]])
            for w in NB[v]:
                legal=[neigh[w] for neigh in [prev,nxt] if w in neigh]
                cnf.append([-var,-(w+1),*legal])
    for v,L in enumerate(occ):
        atmostone(L);cnf.append([-(v+1),*L])
    with Solver(name='cadical195',bootstrap_with=cnf) as sat:
        sat.set_phases([D[v] for v,D in zip(seed,ids)])
        while True:
            remaining=budget-sat.accum_stats()['conflicts']
            if remaining<=0:return 'UNKNOWN',None
            sat.conf_budget(remaining)
            ok=sat.solve_limited()
            if ok is not True:return ('UNKNOWN' if ok is None else 'UNSAT'),None
            model=set(sat.get_model())
            w=[next(v for v,var in D.items() if var in model) for D in ids]
            assert check(w)
            if blacklist is None or canonical([(x^y).bit_length()-1 for x,y in zip(w,w[1:])]) not in blacklist:
                return 'FOUND',w
            sat.add_clause([-D[v] for D,v in zip(ids,w)])

if __name__=='__main__':
    import sys
    source,count,salt=sys.argv[1:4];rng=random.Random(int(salt))
    controls=json.loads(Path('q9_independent_connectors_damaged_control.json').read_text())
    state,w=solve(controls['source'],rng,36,15000,0,set(controls['source_chord'][0]))
    assert state=='FOUND' and len(w)==192 and check(w)
    print(json.dumps(['control',state,len(w)-1,w]),flush=True)
    seeds=[list(map(int,l.split())) for l in Path(source).read_text().splitlines()]
    known=set(Path(sys.argv[4]).read_text().split()) if len(sys.argv)>4 else None
    for i in range(int(count)):
        k=rng.randrange(len(seeds));width=rng.choice((5,8,12,18,24));freeze=rng.choice((.03,.08,.16,.24,.33))
        st,w=solve(seeds[k],rng,width,5000,freeze,blacklist=known)
        print(json.dumps([i,k,width,freeze,st,w],separators=(',',':')),flush=True)
        if w:
            if known is None:break
            known.add(canonical([(x^y).bit_length()-1 for x,y in zip(w,w[1:])]))
            for q in (w,w[::-1]):
                for v in NB[q[-1]]:
                    if check(q+[v]):
                        print(json.dumps(['FOUND192',q+[v]]),flush=True)
                        sys.exit(0)


