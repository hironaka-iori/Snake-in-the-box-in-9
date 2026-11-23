import itertools,json,sys
from collections import Counter
from prepare import D,majority,words,NB,graph
from pysat.solvers import Minicard
def valid(p):
    return len(set(p))==len(p) and all(((a^b).bit_count()==1)==(i+1==j) for (i,a),(j,b) in itertools.combinations(enumerate(p),2))
def solve(A,c,budget,pieces=1):
    k=c['k'];rm=set(c['remove']);add=set(c['added']);drop=set(c['drop']);new=set(c['new']);med=set(c['qs'])
    fixed=(A-drop)|add;allowed=(A-rm)|new;optional=allowed-fixed
    odd={q for q in range(512) if q.bit_count()%2==1 and len(NB[q]&fixed)<=2<=len(NB[q]&allowed)}
    allV=allowed|odd
    if not med<=odd:return 'UNSAT',0,0,None
    with Minicard() as s:
        def ex(lits,k):
            if k<0 or k>len(lits):s.add_clause([]);return
            s.add_atmost(lits,k);s.add_atmost([-v for v in lits],len(lits)-k)
        ex([-(v+1) for v in sorted(drop-rm)],k-len(rm));ex([v+1 for v in sorted(new-add)],k-len(add))
        for q in med:s.add_clause([q+1])
        def conditional(z,lits,k):
            guard=[-z] if z else []
            if not 0<=k<=len(lits):s.add_clause(guard);return
            for t in itertools.combinations(lits,k+1):s.add_clause(guard+[-v for v in t])
            for t in itertools.combinations(lits,len(lits)-k+1):s.add_clause(guard+list(t))
        for q in sorted(odd):
            conditional(q+1,[x+1 for x in sorted(NB[q]&optional)],2-len(NB[q]&fixed))
        ends=[]
        for a in sorted(allowed):
            e=a+513;lits=[q+1 for q in sorted(NB[a]&odd)]
            if a in optional:s.add_clause([-e,a+1])
            conditional(a+1 if a in optional else None,[*lits,e],2);ends.append(e)
        ex(ends,2*pieces);ex([q+1 for q in sorted(odd)],len(A)-pieces)
        phase=[v+1 if v in A else -(v+1) for v in optional]
        s.set_phases(phase);cuts=0
        while True:
            remain=budget-s.accum_stats()['conflicts']
            if remain<=0:return 'UNKNOWN',cuts,budget,None
            s.conf_budget(remain);st=s.solve_limited();conf=s.accum_stats()['conflicts']
            if st is not True:return 'UNSAT' if st is False else 'UNKNOWN',cuts,conf,None
            model=set(s.get_model());S=fixed|{v for v in (optional|odd) if v+1 in model}
            assert len(S)==2*len(A)-pieces
            tips=[v for v in S if len(NB[v]&S)==1];assert len(tips)==2*pieces
            paths=[];rest=set(S)
            for tip in tips:
                if tip not in rest:continue
                p=[tip];rest.remove(tip)
                while NB[p[-1]]&rest:
                    x,=NB[p[-1]]&rest;p.append(x);rest.remove(x)
                paths.append(p)
            if not rest:
                assert len(paths)==pieces and all(valid(p) for p in paths) and len(A-S)==k and med<=S
                return 'FOUND',cuts,conf,paths[0] if pieces==1 else paths
            while rest:
                part=[rest.pop()]
                for x in part:
                    near=NB[x]&rest;part.extend(near);rest-=near
                s.add_clause([-(v+1) for v in part if v not in fixed]);cuts+=1
def main():
    start,stop,budget=map(int,sys.argv[1:]);records=(D/'jobs.jsonl').read_text().splitlines()
    for i in range(start,min(stop,len(records))):
        c=json.loads(records[i]);A=majority(words[c['row']]);st,ns,con,p=solve(A,c,budget)
        print(json.dumps([i,st,ns,con,p],separators=(',',':')),flush=True)
        if p:break
if __name__=='__main__':main()
