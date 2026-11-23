"""Search freely within each four-vertex same-color coset of a 191-edge parent."""
import argparse
import gzip
import json
import random
from itertools import combinations
from pysat.solvers import Minicard, Cadical195
from pysat.card import CardEnc,EncType
from search_q9_wynn_plateau import NB
from verify_q9_center_avoidance import forms,verify


def solve(side,seed,group,budget,control=False,cadical=False):
    # Only occupancy counts of same-color cosets are preserved.
    cosets={}
    for v in range(512):
        key=min(v^t for t in group)
        cosets.setdefault(key,[]).append(v)
    parity=next(iter(side)).bit_count()%2
    profile={k:len(side.intersection(o)) for k,o in cosets.items() if k.bit_count()%2==parity}
    fixed={v for k,n in profile.items() if n==4 for v in cosets[k]}
    possible={v for k,n in profile.items() if n>0 for v in cosets[k]}
    bounds={}
    for w in range(512):
        if w.bit_count()%2==parity:continue
        groups={}
        for v in NB[w]:
            k=min(v^t for t in group)
            groups[k]=groups.get(k,0)+1
        lo=sum(max(0,profile[k]-4+d) for k,d in groups.items())
        hi=sum(min(profile[k],d) for k,d in groups.items())
        if lo<=2 and hi>=1:bounds[w]=(lo,hi)
    allowed=possible|bounds.keys()
    with (Cadical195() if cadical else Minicard()) as sat:
        def equal(guard,lits,k):
            if not 0<=k<=len(lits):
                sat.add_clause(guard);return
            for sub in combinations(lits,k+1):sat.add_clause(guard+[-z for z in sub])
            for sub in combinations(lits,len(lits)-k+1):sat.add_clause(guard+list(sub))
        def cardinal(lits,k):
            if not 0<=k<=len(lits):sat.add_clause([]);return
            if cadical:
                assert k==2
                enc=CardEnc.equals(lits,bound=k,top_id=2048,encoding=EncType.seqcounter)
                sat.append_formula(enc.clauses)
            else:
                sat.add_atmost(lits,k);sat.add_atmost([-z for z in lits],len(lits)-k)
        for k,n in profile.items():
            if 0<n<4:equal([],[v+1 for v in cosets[k]],n)
        tips={w:513+w for w,(lo,hi) in bounds.items() if lo<=1}
        cardinal(list(tips.values()),2)
        # Summing both sides degree by degree implies the majority cardinality.
        if not cadical:cardinal([v+1 for v in bounds],len(side)+1)
        for v in possible:
            guard=[] if v in fixed else [-v-1]
            equal(guard,[w+1 for w in NB[v] if w in bounds],2)
        for w in bounds:
            lits=[v+1 for v in NB[w] if v in possible-fixed]
            if w in tips:
                sat.add_clause([-tips[w],w+1]);lits.append(tips[w])
            equal([-w-1],lits,2-len(fixed.intersection(NB[w])))
        for k,o in cosets.items():
            if k in profile or any(w not in bounds for w in o):continue
            total=sum(len(side.intersection(NB[w])) for w in o)
            equal([-w-1 for w in o],[tips[w] for w in o if w in tips],8-total)
        sat.set_phases([v+1 if v in seed else -v-1 for v in allowed-fixed])
        hints=[v+1 for v in side-fixed] if control else []
        while True:
            left=budget-sat.accum_stats()["conflicts"]
            if left<=0:return "UNKNOWN",None
            sat.conf_budget(left);out=sat.solve_limited(assumptions=hints)
            if out is not True:return ("UNKNOWN" if out is None else "UNSAT"),None
            model=set(sat.get_model())
            selected=fixed|{v for v in allowed-fixed if v+1 in model}
            unseen=set(selected);parts=[]
            while unseen:
                vs=[unseen.pop()]
                for v in vs:
                    for w in NB[v]:
                        if w in unseen:vs.append(w);unseen.remove(w)
                parts.append(set(vs))
            if len(parts)==1:
                w=next(v for v in selected if len(selected.intersection(NB[v]))==1)
                path=[w];rest=selected-{w}
                while rest:
                    w,=rest.intersection(NB[path[-1]])
                    path.append(w);rest.remove(w)
                verify(path);assert len(path)==len(side)*2+1
                assert all(len(set(path[1::2]).intersection(cosets[k]))==n for k,n in profile.items())
                return "FOUND",path
            for comp in parts:
                # If these two representatives survive on opposite sides of the
                # cut, a connected solution must choose a neighbor outside it.
                a=min(comp);b=min(selected-comp)
                border={w for v in comp for w in NB[v] if w in allowed-comp}
                sat.add_clause([w+1 for w in border]+[-v-1 for v in (a,b) if v not in fixed])


def main():
    ap=argparse.ArgumentParser();ap.add_argument("start",type=int);ap.add_argument("stop",type=int)
    ap.add_argument("--count",type=int,default=4);ap.add_argument("--budget",type=int,default=4500)
    opt=ap.parse_args();bank={}
    for line in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,line.split()))
        if len(p)==192:bank.setdefault(forms(p,191)[0],p)
    if opt.start==0:
        q=next(iter(bank.values()))[:-1];verify(q)
        for group in [(0,3,5,6),(0,3,12,15),(0,15,240,255)]:
            st,w=solve(set(q[1::2]),set(q),group,30000,control=True)
            assert st=="FOUND" and len(w)==191
    axes=[t for t in range(1,512) if t.bit_count()==2]
    for i,p in enumerate(bank.values()):
        if not opt.start<=i<opt.stop:continue
        verify(p)
        for s in (0,1):
            rng=random.Random(142955+2*i+s);groups=set()
            while len(groups)<opt.count:
                a,b=rng.sample(axes,2);groups.add(tuple(sorted((0,a,b,a^b))))
            for g in sorted(groups):
                st,w=solve(set(p[s::2]),set(p),g,opt.budget)
                print(json.dumps([i,s,g,st,w],separators=(",",":")),flush=True)
                if w:return


if __name__=="__main__":main()
