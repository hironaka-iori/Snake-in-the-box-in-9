"""Choose an induced path in the union of two isometrically aligned Q9 records."""
import argparse
import json
import random
from collections import Counter, defaultdict
from itertools import combinations
from pysat.solvers import Minicard

ALL=set(range(512))
NB=[[x^(1<<d) for d in range(9)] for x in range(512)]

def verify(p):
    assert len(p)==len(set(p)) and set(p)<=ALL
    for i,x in enumerate(p):
        assert {y for y in NB[x] if y in setp(p)} == set(p[max(0,i-1):i]+p[i+1:i+2])

def setp(p):
    return set(p)

def norm(steps):
    mapping={}
    return bytes(mapping.setdefault(d,len(mapping)) for d in steps),list(mapping)

def solve(domain,seed,target,budget):
    # Vertex x uses x+1, an endpoint uses x+513. The two endpoints may be anywhere.
    with Minicard() as sat:
        ends=[]
        for x in sorted(domain):
            s=x+1;e=x+513;ends.append(e)
            nei=[y+1 for y in NB[x] if y in domain]
            sat.add_clause([-e,s])
            sat.add_clause([-s,*nei])
            for a,b,c in combinations(nei,3):sat.add_clause([-s,-a,-b,-c])
            for a,b in combinations(nei,2):sat.add_clause([-e,-a,-b])
            for j in range(len(nei)):sat.add_clause([-s,e,*nei[:j],*nei[j+1:]])
        def exact(lits,count):
            sat.add_atmost(lits,count)
            sat.add_atmost([-x for x in lits],len(lits)-count)
        if len(domain)<target+1:return "UNSAT",None,0
        exact(ends,2)
        exact([x+1 for x in domain],target+1)
        if target%2==0:
            parity=1025
            for x in domain:
                sat.add_clause([-(x+513),parity if x.bit_count()%2 else -parity])
        sat.set_phases([x+1 if x in seed else -(x+1) for x in sorted(domain)])
        cuts=0
        while True:
            remaining=budget-sat.accum_stats()["conflicts"]
            if remaining<=0:return "UNKNOWN",None,cuts
            sat.conf_budget(remaining)
            result=sat.solve_limited()
            if result is not True:return ("UNKNOWN" if result is None else "UNSAT"),None,cuts
            model=set(sat.get_model())
            selected={x for x in domain if x+1 in model}
            tips=[x for x in selected if x+513 in model]
            assert len(tips)==2
            def component(start):
                seen=set();seq=[];v=start
                while v is not None:
                    seq.append(v);seen.add(v)
                    v=next((z for z in NB[v] if z in selected and z not in seen),None)
                return seq
            path=component(tips[0]);remainder=selected-set(path)
            if not remainder:
                verify(path);assert len(path)==target+1
                return "FOUND",path,cuts
            while remainder:
                cycle=component(next(iter(remainder)))
                assert all(sum(z in selected for z in NB[v])==2 for v in cycle)
                sat.add_clause([-(x+1) for x in cycle])
                cuts+=1;remainder.difference_update(cycle)

def alignments(bank,tries,seed):
    rng=random.Random(seed);walks=[];groups=defaultdict(list)
    for line in open(bank):
        n,*s=map(int,line.split());assert n==9 and len(s)==191
        for seq in (s,s[::-1]):
            p=[0]
            for d in seq:p.append(p[-1]^(1<<d))
            verify(p);ix=len(walks);walks.append(p)
            for i in range(0,len(seq)-13,3):
                sig,dims=norm(seq[i:i+14]);groups[sig].append((ix,i,dims))
    valid=[g for g in groups.values() if len(g)>1]
    seen=set()
    for _ in range(tries):
        (a,i,da),(b,j,db)=rng.sample(rng.choice(valid),2)
        if a==b:continue
        ex=list(set(range(9))-set(da));rng.shuffle(ex)
        dmap=dict(zip(db+sorted(set(range(9))-set(db)),da+ex))
        off=walks[a][i];q=[off]
        for x,y in zip(walks[b][j::-1],walks[b][j-1::-1] if j else []):
            q.append(q[-1]^(1<<dmap[(x^y).bit_length()-1]))
        q.reverse()
        for x,y in zip(walks[b][j:],walks[b][j+1:]):
            q.append(q[-1]^(1<<dmap[(x^y).bit_length()-1]))
        p=walks[a]
        assert len(q)==len(p) and q[j:j+15]==p[i:i+15]
        dom=frozenset([*p,*q])
        if not 193<=len(dom)<=246 or dom in seen:continue
        seen.add(dom)
        yield dom,p,q,rng

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--bank',default='/tmp/q9_project_records_input9')
    ap.add_argument('--cases',type=int,default=2600);ap.add_argument('--cap',type=int,default=4000)
    ap.add_argument('--seed',type=int,default=2001398);ap.add_argument('--target',type=int,default=192)
    ap.add_argument('--extra',type=int,default=0)
    args=ap.parse_args()
    for i,(domain,p,q,rng) in enumerate(alignments(args.bank,300000,args.seed)):
        if args.extra:
            # Include vertices that cost few deletions in at least one parent to insert.
            ds=[set(p),set(q)]
            def rank(v):
                return (min(abs(sum(w in a for w in NB[v])-2) for a in ds),
                        -sum(x in domain for x in NB[v]),rng.random())
            domain=domain.union(sorted(ALL-domain,key=rank)[:args.extra])
        st,w,cuts=solve(domain,set(p),args.target,args.cap)
        print(json.dumps([st,hex(sum(1<<x for x in domain)),cuts,w],separators=(",",":")),flush=True)
        if w or i+1>=args.cases:break
