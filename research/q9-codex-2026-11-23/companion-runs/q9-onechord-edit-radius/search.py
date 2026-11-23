"""Exact replacement radius on an induced-path vertex set, using Max-k SAT."""
from collections import Counter
import argparse,json,time
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import CNF
from pysat.solvers import Cadical195, Minicard
NB=[tuple(x^(1<<i) for i in range(9)) for x in range(512)]
def validate(p):
    assert len(p)==len(set(p)) and all(0<=x<512 for x in p)
    assert all(((x^y).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j,y in enumerate(p) if j>i)
def search(p,k,budget,native=False,consequence=False):
    S=set(p);outside=set(range(512))-S;vars0=[x+1 for x in sorted(S)];vars1=[x+1 for x in sorted(outside)]
    cnf=CNF();top=1024
    def maxk(v,k):
        nonlocal top
        if k>=len(v):return
        if k<0:cnf.append([]);return
        c=CardEnc.atmost(v,bound=k,top_id=top,encoding=EncType.seqcounter);cnf.extend(c);top=max(top,c.nv)
    # Count replacement variables, with small bounds, on either polarity.
    # At least k removals/additions uses the same counter via exact totalizer
    # variables implementing a bidirectional recurrence, truncated to k+1.
    def count(v,k):
        nonlocal top
        prev=[]
        for i,lit in enumerate(v):
            curr=[]
            for j in range(min(k+1,i+1)):
                top+=1;z=top;curr.append(z);a=prev[j] if j<len(prev) else None;b=prev[j-1] if j>0 else None
                if a is not None:cnf.append([-a,z])
                if j==0:cnf.append([-lit,z])
                else:cnf.append([-lit,-b,z])
                if a is None:cnf.append([-z,lit]);cnf.append([-z,b] if j else [-z,lit])
                elif j==0:cnf.append([-z,a,lit])
                else:cnf.append([-z,a,lit]);cnf.append([-z,a,b])
            prev=curr
        cnf.append([prev[k-1]]);cnf.append([-prev[k]])
    ends=[513+x for x in range(512)]
    if not native:
        count([-v for v in vars0],k);count(vars1,k);count(ends,2)
    for x,ns in enumerate(NB):
        s=x+1;e=x+513;nei=[v+1 for v in ns]
        cnf.append([-e,s]);cnf.append([-s,*nei])
        for y,z in combinations(nei,2):cnf.append([-e,-y,-z])
        for a,b,c in combinations(nei,3):cnf.append([-s,-a,-b,-c])
        for i in range(9):cnf.append([-s,e,*nei[:i],*nei[i+1:]])
    if consequence:
        # For any selected new vertex, enough old neighbors must disappear.
        # Each surviving old neighbor must in turn have a spare incidence.
        for x in sorted(outside):
            old_ns=[y for y in NB[x] if y in S]
            if len(old_ns)>k+2:cnf.append([-x-1])
            for n in old_ns:
                for u,v in combinations([v for v in NB[n] if v in S],2):
                    cnf.append([-x-1,-n-1,-u-1,-v-1])
    with (Minicard(bootstrap_with=cnf) if native else Cadical195(bootstrap_with=cnf)) as sol:
        if native:
            for lits,n in [([-v for v in vars0],k),(vars1,k),(ends,2)]:
                sol.add_atmost(lits,n);sol.add_atmost([-v for v in lits],len(lits)-n)
        sol.set_phases(vars0+[-v for v in vars1])
        if consequence and native:
            for x in outside:
                old_ns=[n+1 for n in NB[x] if n in S]
                # AddAtMost is unconditional; use clauses encoding the gate
                # plus every forbidden triple. Retain a strong phase hint.
                for a,b,c in combinations(old_ns,3):
                    sol.add_clause([-x-1,-a,-b,-c])
        cuts=0
        while True:
            rem=budget-sol.accum_stats()['conflicts']
            if rem<=0:return 'UNKNOWN',None,cuts,sol.accum_stats()['conflicts']
            sol.conf_budget(rem);r=sol.solve_limited()
            if r is not True:return 'UNSAT' if r is False else 'UNKNOWN',None,cuts,sol.accum_stats()['conflicts']
            model=set(sol.get_model());chosen={x for x in range(512) if x+1 in model}
            assert len(S-chosen)==len(chosen-S)==k
            endpoints=[x for x in chosen if x+513 in model];assert len(endpoints)==2
            seen=set();seq=[];v=endpoints[0]
            while v is not None:
                seq.append(v);seen.add(v);v=next((w for w in NB[v] if w in chosen-seen),None)
            if chosen==seen:
                validate(seq);return 'FOUND',seq,cuts,sol.accum_stats()['conflicts']
            rest=chosen-seen
            while rest:
                component=[rest.pop()]
                for v in component:
                    for w in NB[v]:
                        if w in rest:rest.remove(w);component.append(w)
                # A full selected cycle permanently saturates each of its vertices.
                sol.add_clause([-v-1 for v in component]);cuts+=1
def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('out',type=Path)
    ap.add_argument('k',type=int);ap.add_argument('budget',type=int);ap.add_argument('start',type=int);ap.add_argument('stop',type=int)
    ap.add_argument('--stride',type=int,default=1);ap.add_argument('--control',action='store_true');ap.add_argument('--native',action='store_true');ap.add_argument('--extra',action='store_true')
    a=ap.parse_args();rows=[list(map(int,l.split())) for l in a.input.read_text().splitlines()];cnt=Counter()
    with a.out.open('w') as f:
        for i in range(a.start,min(a.stop,len(rows)),a.stride):
            p=rows[i];assert len(set(p))==len(p) and all(0<=v<512 for v in p) and all((x^y).bit_count()==1 for x,y in zip(p,p[1:]))
            chords=[(u,v) for j,u in enumerate(p) for v in p[j+2:] if (u^v).bit_count()==1]
            if not a.control:assert len(p)==193 and len(chords)==1
            t=time.monotonic();st,w,cut,conf=search(p,a.k,a.budget,a.native,a.extra)
            d=dict(index=i,k=a.k,status=st,cycle_cuts=cut,conflicts=conf,seconds=round(time.monotonic()-t,3),chords=chords)
            if w:d.update(vertices=w,deleted=sorted(set(p)-set(w)),added=sorted(set(w)-set(p)))
            print(json.dumps(d,separators=(',',':')),file=f,flush=True);cnt[st]+=1
            if w:break
    print(cnt,flush=True)
if __name__=='__main__':main()
