"""Bounded SAT searches with no prescribed ports; every found model is checked explicitly."""
from itertools import combinations
from pathlib import Path
from collections import Counter
import sys,time,json
from pysat.solvers import Cadical195
from pysat.card import CardEnc,EncType
from pysat.formula import CNF
from verify_q9_222_disconnected import components

def search(mode, budget, pair_cuts=None):
    q=6 if mode=="tiles" else 9
    n=1<<q
    copies=2 if mode=="tiles" else 1
    cnf=CNF(); top=n*copies
    def card(xs,target):
        nonlocal top
        f=CardEnc.equals(xs,target,top_id=top,encoding=EncType.totalizer);cnf.extend(f.clauses);top=f.nv
    def lit(c,v):return 1+c*n+v
    ends=[]
    if copies==2:
        for v in range(n):cnf.append([-lit(0,v),-lit(1,v)])
        # Each of the two sets appears four times in Q9; 56*4=224.
        card(list(range(1,129)),56)
        cnf.append([1])
    else:
        for par in (0,1):card([v+1 for v in range(n) if v.bit_count()%2==par],111)
        # Translation and permutation of axes place one endpoint and its first edge.
        cnf.extend([[1],[2]]+[[-(1<<i)-1] for i in range(1,9)])
    for c in range(copies):
        for v in range(n):
            ns=[lit(c,v^(1<<i)) for i in range(q)]; guard=-lit(c,v)
            for triple in combinations(ns,3):cnf.append([guard]+[-x for x in triple])
            if copies==1:
                top+=1;end=top;ends.append(end)
                cnf.append([-end,lit(c,v)])
                if v==0:cnf.append([end])
                for a,b in combinations(ns,2):cnf.append([-end,-a,-b])
                cnf.append([guard]+ns)
            for missing in range(q):cnf.append([guard]+([end] if copies==1 else [])+ns[:missing]+ns[missing+1:])
    if ends:card(ends,2)
    for c in range(copies):
        for a,b in combinations(range(q),2):
            mask=(1<<a)|(1<<b)
            for v in range(n):
                if not v&mask:cnf.append([-lit(c,v^t) for t in [0,1<<a,1<<b,mask]])
    if pair_cuts:top=pair_cuts(cnf,top)
    cuts=Counter(); rounds=0
    with Cadical195(bootstrap_with=cnf) as sat:
        while True:
            left=budget-sat.accum_stats()["conflicts"]
            if left<=0:res=None
            else:sat.conf_budget(left);res=sat.solve_limited()
            if res is not True:
                print(json.dumps(dict(mode=mode,status="UNKNOWN" if res is None else "UNSAT_unverified",rounds=rounds,cuts=dict(cuts),stats=sat.accum_stats())),flush=True);return
            m=set(sat.get_model());bad=[]
            sets=[{v for v in range(n) if lit(c,v) in m} for c in range(copies)]
            for c,S in enumerate(sets):
                for C in components(S):
                    iscycle=all(sum((v^(1<<i)) in C for i in range(q))==2 for v in C)
                    if iscycle and (copies==1 or (max_span(C)<=5)):
                        bad.append((c,C));cuts[str((len(C),max_span(C)))]+=1
            rounds+=1
            if not bad:
                print(json.dumps(dict(mode=mode,status="FOUND",rounds=rounds,sets=[sorted(S) for S in sets],cuts=dict(cuts))),flush=True);return
            for c,C in bad:sat.add_clause([-lit(c,v) for v in sorted(C)])
def max_span(C):
    a=min(C);z=0
    for v in C:z|=v^a
    return z.bit_count()
if __name__=="__main__":search(sys.argv[1],int(sys.argv[2]))
