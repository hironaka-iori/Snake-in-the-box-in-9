"""Alternate which half of Q9 is held fixed, accepting novel paths across multiple lengths."""
import gzip
import json
import random
import sys
from collections import Counter
from itertools import combinations
from pysat.solvers import Minicard
from search_q9_unordered_projection import project
from verify_q9_center_avoidance import verify,code,forms

def half_completion(A, target, budget, hint, reject=None):
    c=(next(iter(A))%256).bit_count()%2
    columns=[v for v in range(256) if v.bit_count()%2!=c]
    def fixed_nb(x):
        return [x^(1<<d) for d in range(8) if x^(1<<d) in A]
    ends=[];free=set();allowed={}
    for v in columns:
        states=[]
        for state in range(4):
            selected=[v+256*b for b in range(2) if state&(1<<b)]
            degrees=[len(fixed_nb(x))+(state==3) for x in selected]
            if all(1<=n<=2 for n in degrees):
                states.append((state,selected,degrees));free.update(selected)
        allowed[v]=states
    if sum(max(len(s) for _,s,_ in seq) for seq in allowed.values())+len(A)<=target:return 'SIZE',None
    with Minicard() as sat:
        def atleast(lits,k):
            if k>len(lits):sat.add_clause([])
            elif k>0:sat.add_atmost([-v for v in lits],len(lits)-k)
        for v,states in allowed.items():
            a,b=v+1,v+257
            for state in range(4):
                deny=[-a if state&1 else a,-b if state&2 else b]
                match=next((s for s in states if s[0]==state),None)
                if match is None:sat.add_clause(deny);continue
                _,selected,degrees=match
                for x in (v,v+256):
                    if x in free:
                        active=x in selected and degrees[selected.index(x)]==1
                        sat.add_clause(deny+[x+513 if active else -x-513])
        ends.extend(x+513 for x in free)
        for x in A:
            vertical=int((x^256) in A)
            ns=[v+1 for v in (x^(1<<d) for d in range(8)) if v in free]
            if len(ns)<1-vertical:return 'DEGREE',None
            if not vertical:sat.add_clause(ns)
            for bad in combinations(ns,3-vertical):sat.add_clause([-z for z in bad])
            e=x+513;ends.append(e)
            for bad in combinations(ns,2-vertical):sat.add_clause([-e,*(-z for z in bad)])
            if vertical:sat.add_clause([e,*ns])
            else:
                for j in range(len(ns)):sat.add_clause([e,*ns[:j],*ns[j+1:]])
        sat.add_atmost(ends,2);atleast(ends,2);atleast([x+1 for x in free],target+1-len(A))
        sat.set_phases([x+1 if x in hint else -x-1 for x in free])
        while True:
            rem=budget-sat.accum_stats()['conflicts']
            if rem<=0:return 'UNKNOWN',None
            sat.conf_budget(rem);ok=sat.solve_limited()
            if ok is not True:return ('UNKNOWN' if ok is None else 'UNSAT'),None
            m=set(sat.get_model());chosen=A|{x for x in free if x+1 in m}
            nb=lambda x:{x^(1<<d) for d in range(9)}&chosen
            tips=[x for x in chosen if len(nb(x))==1];assert len(tips)==2
            p=tips[:1];rest=set(chosen)-set(p)
            while q:=nb(p[-1])&rest:
                assert len(q)==1
                y=q.pop();p.append(y);rest.remove(y)
            if not rest:
                verify(p);assert len(p)>target
                if not reject or not reject(p):return 'FOUND',p
                sat.add_clause([-(x+1) if x in chosen else x+1 for x in free]);continue
            while rest:
                comp=[rest.pop()]
                for y in comp:
                    new=nb(y)&rest;comp.extend(new);rest-=new
                sat.add_clause([-y-1 for y in comp if y in free])

def shape(p):
    return code([a^b for a,b in zip(p,p[1:])])

def main():
    rng=random.Random(198291);runs=int(sys.argv[1])
    public=[list(map(int,line.split())) for line in gzip.open('q9_port_followup_public191.txt.gz','rt')]
    h=project(public[0],8);A={v for v in h if (v%256).bit_count()%2==0}
    st,w=half_completion(A,191,100000,set());assert st=='FOUND';verify(w);print(json.dumps(['control',191,w]),flush=True)
    bank=[r['vertices'] for r in map(json.loads,open('q9_neutral_eligible_growth.jsonl')) if r.get('edges')==189]
    rng.shuffle(bank);bank=bank[:800];seen={shape(p) for p in bank+public};fixed=set()
    blocked={bytes(map(int,s)) for s in open('q9_excluded_142_lex.txt').read().split()}
    for i in range(runs):
        root=rng.choice(bank[-100:]) if i%3==0 else rng.choice(bank)
        h=project(root,rng.randrange(9));c=rng.randrange(2)
        A=frozenset(v for v in h if (v%256).bit_count()%2==c)
        if A in fixed:continue
        fixed.add(A)
        def reject(p):return len(p)<193 and (shape(p) in seen or not blocked.isdisjoint(forms(p,142)))
        for target in (192,191,190,189):
            st,w=half_completion(A,target,9000,h,reject if target<192 else None)
            print(json.dumps([i,target,st,w],separators=(',',':')),flush=True)
            if w:
                verify(w)
                if len(w)>=193:return
                seen.add(shape(w));bank.append(w);break
if __name__=='__main__':main()
