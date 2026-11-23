"""Search every visiting order on a fixed set of occupied Q8 projection columns."""
import argparse
import gzip
import json
import random
from itertools import combinations
from pysat.solvers import Minicard
from verify_q9_center_avoidance import verify

def project(p,d):
    def col(v):
        return (v & ((1<<d)-1)) | ((v>>(d+1))<<d)
    return {col(v)+256*((v>>d)&1) for v in p}

def solve(hint,goal,budget,atleast=False):
    S={v%256 for v in hint}
    nb={v:{v^(1<<d) for d in range(8)} & S for v in S}
    if abs(sum(1 if v.bit_count()%2 else -1 for v in S))>1 or sum(len(a)==1 for a in nb.values())>2:
        return "PROJECTION",None
    if S:
        reached={next(iter(S))};todo=list(reached)
        for v in todo:
            extra=nb[v]-reached;todo.extend(extra);reached.update(extra)
        if reached!=S:return "PROJECTION",None
    free={v for v in S if len(nb[v])<=2}
    k=goal+1-len(S)
    if k<0 or k>len(free):return "SIZE",None
    with Minicard() as sat:
        def exact(lits,n):
            sat.add_atmost(lits,n)
            sat.add_atmost([-l for l in lits],len(lits)-n)
        for v in S:
            a=v+1;b=a+256;t=v+513
            sat.add_clause([a,b])
            if v in free:
                sat.add_clause([-t,a]);sat.add_clause([-t,b]);sat.add_clause([-a,-b,t])
                for w in nb[v]&free:
                    if v<w:sat.add_clause([-t,-w-513])
            else:sat.add_clause([-a,-b])
        specials=sorted(S-free)
        if specials:
            v=specials[0]
            sat.add_clause([v+1 if v in hint else v+257])
        if atleast:sat.add_atmost([-v-513 for v in free],len(free)-k)
        else:exact([v+513 for v in free],k)
        ends=[];pool=S|{256+v for v in S}
        for x in pool:
            X=x+1;e=x+769;ends.append(e)
            neighbors=[(w^(x&256))+1 for w in nb[x%256]]+[(x^256)+1]
            sat.add_clause([-e,X]);sat.add_clause([-X,*neighbors])
            for a,b in combinations(neighbors,2):sat.add_clause([-e,-a,-b])
            for a,b,c in combinations(neighbors,3):sat.add_clause([-X,-a,-b,-c])
            for j in range(len(neighbors)):sat.add_clause([-X,e,*neighbors[:j],*neighbors[j+1:]])
            if goal%2==0 and not atleast:sat.add_clause([-e,1400 if x.bit_count()%2 else -1400])
        exact(ends,2)
        sat.set_phases([v+1 if v in hint else -(v+1) for v in pool])
        while True:
            rem=budget-sat.accum_stats()['conflicts']
            if rem<=0:return "UNKNOWN",None
            sat.conf_budget(rem);res=sat.solve_limited()
            if res is not True:return ("UNSAT" if res is False else "UNKNOWN"),None
            m=set(sat.get_model());chosen={x for x in pool if x+1 in m}
            adjacent=lambda x:{x^(1<<d) for d in range(9)} & chosen
            p=[next(x for x in chosen if len(adjacent(x))==1)]
            rest=chosen-set(p)
            while q:=adjacent(p[-1])&rest:
                assert len(q)==1
                v=q.pop();p.append(v);rest.remove(v)
            if not rest:
                verify(p);assert {v%256 for v in p}==S and (len(p)>=goal+1 if atleast else len(p)==goal+1)
                return 'FOUND',p
            while rest:
                comp=[rest.pop()]
                for v in comp:
                    q=adjacent(v)&rest;comp.extend(q);rest-=q
                sat.add_clause([-v-1 for v in comp])

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('file');ap.add_argument('cases',type=int);ap.add_argument('budget',type=int);ap.add_argument('--skip',type=int,default=0);ap.add_argument('--sections',action='store_true');ap.add_argument('--atleast',action='store_true');ap.add_argument('--alter',type=int,default=0);args=ap.parse_args()
    rng=random.Random(7182)
    stream=gzip.open(args.file,'rt') if args.file.endswith('.gz') else open(args.file)
    paths=[list(map(int,s.split())) for s in stream]
    if args.sections:
        assert all(len(row)==row[2]+3 and len(set(row[3:]))==row[2] for row in paths)
        paths=[row[3:] for row in paths]
    ctrl=json.load(open('q9_explicit_q8_96_plus_94.json'))['vertices']
    st,w=solve(project(ctrl,8),191,50000);assert st=='FOUND'
    print(json.dumps(['control',191,st,w]),flush=True)
    jobs=[(i,d) for i in range(len(paths)) for d in range(9)];rng.shuffle(jobs);seen=set()
    for i,d in jobs:
        h=project(paths[i],d);S={v%256 for v in h}
        if args.alter:
            leaves=[v for v in S if sum(v^(1<<k) in S for k in range(8))<=2]
            outside=sorted({v^(1<<k) for v in S for k in range(8)}-S)
            x=rng.choice(sorted(leaves));y=rng.choice(outside)
            h-={x,x+256};h.add(y)
        key=tuple(sorted({v%256 for v in h}))
        if key in seen:continue
        seen.add(key)
        if len(seen)<=args.skip:continue
        st,w=solve(h,192,args.budget,args.atleast)
        print(json.dumps([i,d,st,w],separators=(',',':')),flush=True)
        if w or len(seen)>=args.cases:break
