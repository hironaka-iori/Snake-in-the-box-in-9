"""Lift a prescribed sequence of pair labels, with all individual steps inside a pair free."""
from pathlib import Path
from itertools import combinations
import argparse,collections,json,random
from pysat.solvers import Cadical195
D=Path(__file__).resolve().parent
def partition(ds):
    if not ds:
        yield ()
        return
    a=ds[0]
    for b in ds[1:]:
        rem=tuple(v for v in ds if v not in (a,b))
        for tail in partition(rem):yield ((a,b),)+tail
def axes(word):
    p=[0]
    for d in word:p.append(p[-1]^1<<d)
    return p
def validate(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(((v^u).bit_count()==1)==(i+1==j) for j,v in enumerate(p) for i,u in enumerate(p[:j]))
def lift(w,pairs,single,cap):
    gr={a:k for k,pair in enumerate(pairs) for a in pair};gr[single]=len(pairs)
    grouped=[gr[c] for c in w];ng=len(pairs);coords=[[] for _ in pairs];clock=[0]*ng;frames=[];fibers=collections.defaultdict(list);phase=[];vars=0
    for g in range(ng):
        vars+=1;coords[g].append(vars);phase.append(-vars)
    prev=0;total=0;seed=0
    for t in range(len(w)+1):
        if t:
            axis=w[t-1];k=grouped[t-1];prev^=1<<k;seed^=1<<axis
            if k<ng:
                clock[k]+=1;vars+=1;coords[k].append(vars)
                phase.append(vars if seed&(1<<pairs[k][0]) else -vars)
        frames.append(tuple(coords[k][clock[k]] for k in range(ng)));fibers[prev].append(t)
    assert len(w)%2==0
    # Start each pair at 00. Symmetry under exchanging the two axes fixes its first step.
    clauses=[[-row[0]] for row in coords];preferred=set(phase)
    for row in coords:
        if len(row)>1:clauses.append([row[1] if row[1] in preferred else -row[1]])
    varfor={};demands=set()
    for mask,ts in fibers.items():
        for change in [-1,*range(ng+1)]:
            other=mask if change<0 else mask^1<<change
            if other<mask or other not in fibers:continue
            for t in ts:
                for u in fibers[other]:
                    if (other==mask and t>=u) or abs(t-u)<=1:continue
                    d=tuple(sorted((min(x,y),max(x,y)) for g,(x,y) in enumerate(zip(frames[t],frames[u])) if g!=change and x!=y))
                    if not d:return 'UNSAT',None,0
                    demands.add(d)
    for d in sorted(demands,key=len):
        clause=[]
        for x,y in d:
            if (x,y) not in varfor:
                vars+=1;varfor[x,y]=vars
                clauses.extend(([-vars,x,y],[-vars,-x,-y]))
            clause.append(varfor[x,y])
        clauses.append(clause)
    tip_axes=[]
    axis_list=[v for g in pairs for v in g]+[single]
    mask_at=[0]*(len(w)+1)
    for i,g in enumerate(grouped):mask_at[i+1]=mask_at[i]^1<<g
    signed_terms={}
    for tip in [0,len(w)]:
        selectors={}
        for axis in axis_list:
            vars+=1;gate=vars;selectors[axis]=gate;g=gr[axis]
            mm=mask_at[tip]^1<<g
            for i in range(0,len(w)+1,2):
                if i==tip:continue
                diff=mm^mask_at[i]
                if diff.bit_count()>1:continue
                assert diff.bit_count()==1;omit=diff.bit_length()-1;cl=[-gate];always=False
                for k,(a,b) in enumerate(zip(frames[tip],frames[i])):
                    if k==omit:continue
                    if pairs[k][0]==axis:a=-a
                    if a==-b:always=True;break
                    if a==b:continue
                    key=min(tuple(sorted((a,b))),tuple(sorted((-a,-b))))
                    if key not in signed_terms:
                        vars+=1;signed_terms[key]=vars;clauses.extend(([-vars,a,b],[-vars,-a,-b]))
                    cl.append(signed_terms[key])
                if not always:clauses.append(cl)
        clauses.append(list(selectors.values()));tip_axes.append(selectors)
    with Cadical195(bootstrap_with=clauses) as sol:
        sol.set_phases(phase);sol.conf_budget(cap);r=sol.solve_limited();used=sol.accum_stats()['conflicts']
        if r!=True:return ('UNSAT' if r is False else 'UNKNOWN'),None,used
        model=set(sol.get_model());recovered=[];p=0;ct=[0]*ng
        for g in grouped:
            if g==ng:a=single
            else:
                v=coords[g][ct[g]];ct[g]+=1;y=coords[g][ct[g]]
                a=pairs[g][0 if ((v in model)!=(y in model)) else 1]
            recovered.append(a)
        core=axes(recovered);ends=[next(a for a,v in opts.items() if v in model) for opts in tip_axes]
        out=[core[0]^(1<<ends[0])]+core+[core[-1]^(1<<ends[1])]
        assert validate(out) and len(out)==len(w)+3
        return 'FOUND',out,used
