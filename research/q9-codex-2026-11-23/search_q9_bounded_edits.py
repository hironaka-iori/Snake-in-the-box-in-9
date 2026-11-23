"""Exact vertex-set search within a replacement radius; cycles are cut lazily."""
import argparse
import json
from itertools import combinations,product
from pathlib import Path
from pysat.solvers import Minicard
from verify_q9_center_avoidance import verify
N=[{x^(1<<d) for d in range(9)} for x in range(512)]

def supports(v,old,r):
    # If v is added, <=2 old neighbors can stay. Each such neighbor may have
    # at most one remaining old neighbor besides v. Enumerate who can stay.
    near=N[v]&old
    if len(near)>r+2:return []
    candidates=set()
    for k in range(min(2,len(near)),-1,-1):
        for keep in combinations(near,k):
            removed=near.difference(keep)
            if len(removed)>r:continue
            choices=[]
            for w in keep:
                current=N[w]&old
                choices.append([current-{x} for x in current] or [set()])
            for sets in product(*choices):
                support=frozenset(removed.union(*sets))
                if len(support)<=r:candidates.add(support)
    minimal=[]
    for support in sorted(candidates,key=lambda x:(len(x),sorted(x))):
        if not any(s<=support for s in minimal):minimal.append(support)
    return minimal

def solve(p,r,budget,counts=None):
    old=set(p)
    options={v:ss for v in range(512) if v not in old and (ss:=supports(v,old,r))}
    if counts:
        drops,adds=counts
        options={v:[s for s in choices if all(sum(w.bit_count()%2==c for w in s)<=drops[c] for c in (0,1))] for v,choices in options.items() if adds[v.bit_count()%2]}
        options={v:s for v,s in options.items() if s}
    pool=old|options.keys()
    with Minicard() as sat:
        def exact(lits,n):
            if n<0 or n>len(lits):sat.add_clause([]);return
            sat.add_atmost(lits,n)
            sat.add_atmost([-x for x in lits],len(lits)-n)
        if counts:
            for c in (0,1):
                exact([-v-1 for v in old if v.bit_count()%2==c],drops[c])
                exact([v+1 for v in pool-old if v.bit_count()%2==c],adds[c])
        else:
            sat.add_atmost([-v-1 for v in old],r)
            sat.add_atmost([v+1 for v in pool-old],r)
            exact([v+1 for v in pool],len(old))
        for side in (0,1):
            sat.add_atmost([v+1 for v in pool if v.bit_count()%2==side],(len(p)+1)//2)
        ids={}
        for v,choices in options.items():
            if not choices[0]:continue
            terms=[]
            for support in choices:
                if len(support)==1:
                    terms.append(-next(iter(support))-1)
                else:
                    if support not in ids:
                        ids[support]=len(ids)+1025
                        for w in support:sat.add_clause([-ids[support],-w-1])
                    terms.append(ids[support])
            sat.add_clause([-v-1,*terms])
        # Two new vertices must share a deletion budget. If even their
        # cheapest compatible local supports exceed it, they cannot coexist.
        masks={v:[sum(1<<z for z in s) for s in ss] for v,ss in options.items()}
        for a,b in combinations(options,2):
            if len(options[a][0])+len(options[b][0])<=r:continue
            if not any((i|j).bit_count()<=r for i in masks[a] for j in masks[b]):
                sat.add_clause([-a-1,-b-1])
        for v in pool:
            for a,b in combinations((w for w in N[v]&pool if w>v),2):
                z=v^a^b
                if z>v and z in pool:sat.add_clause([-v-1,-a-1,-b-1,-z-1])
        ends=[]
        for v in pool:
            x=v+1;e=v+513;ends.append(e)
            ns=[w+1 for w in N[v]&pool]
            sat.add_clause([-e,x]);sat.add_clause([-x,*ns])
            for a,b in combinations(ns,2):sat.add_clause([-e,-a,-b])
            for a,b,c in combinations(ns,3):sat.add_clause([-x,-a,-b,-c])
            for j in range(len(ns)):sat.add_clause([-x,e,*ns[:j],*ns[j+1:]])
        exact(ends,2)
        sat.set_phases([v+1 if v in old else -(v+1) for v in pool])
        cuts=0
        while True:
            rem=budget-sat.accum_stats()['conflicts']
            if rem<=0:return 'UNKNOWN',len(pool),cuts,None
            sat.conf_budget(rem);answer=sat.solve_limited()
            if answer is not True:return ('UNKNOWN' if answer is None else 'UNSAT'),len(pool),cuts,None
            model=set(sat.get_model());S={v for v in pool if v+1 in model}
            end=next(v for v in S if len(N[v]&S)==1);path=[end];rest=S-{end}
            while q:=N[path[-1]]&rest:
                assert len(q)==1
                v=q.pop();path.append(v);rest.remove(v)
            if not rest:
                verify(path);assert len(path)==len(p) and len(S-old)<=r
                return 'FOUND',len(pool),cuts,path
            while rest:
                bag=[rest.pop()]
                for v in bag:
                    new=N[v]&rest;bag.extend(new);rest-=new
                sat.add_clause([-v-1 for v in bag]);cuts+=1

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('source');ap.add_argument('radius',type=int);ap.add_argument('budget',type=int);a=ap.parse_args()
    control=json.loads(Path('q9_independent_connectors_damaged_control.json').read_text())['source']
    result=solve(control,1,10000);assert result[0]=='FOUND'
    print(json.dumps(['control',1,*result]),flush=True)
    for i,l in enumerate(Path(a.source).read_text().splitlines()):
        p=list(map(int,l.split()));result=solve(p,a.radius,a.budget)
        print(json.dumps([i,a.radius,*result],separators=(',',':')),flush=True)
        if result[0]=='FOUND':break
