"""Variable crossing times plus independent swaps of projected steps in different clock groups."""
from sheet import ROOT,valid
from collections import defaultdict
from random import Random
from pysat.formula import IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
import json,sys

def search(word,pairs,s,target,swaps,cap):
    gr={a:i for i,pair in enumerate(pairs) for a in pair};seq=[a for a in word if a!=s];m=len(seq);ng=len(pairs)
    if target>2*m+1:return 'UNSAT',None
    pool=IDPool();cl=[];warm=[];fv=[pool.id() for p in pairs];cl.extend([[-v] for v in fv])
    frames=[tuple(fv)];masks=[0];seen=set();x=0
    for a in seq:
        g=gr[a];x^=1<<a;fv[g]=pool.id();frames.append(tuple(fv));masks.append(masks[-1]^(1<<g))
        lit=fv[g] if x&(1<<pairs[g][0]) else -fv[g];warm.append(lit)
        if g not in seen:cl.append([lit]);seen.add(g)
    slots=[[(mask,f,None)] for mask,f in zip(masks,frames)]
    assert all(j-i>=2 for i,j in zip(sorted(swaps),sorted(swaps)[1:]))
    for i in swaps:
        g,h=gr[seq[i]],gr[seq[i+1]]
        if g==h:continue
        y=pool.id();warm.append(-y)
        alt=list(frames[i]);alt[h]=frames[i+2][h]
        slots[i+1]=[(masks[i+1],frames[i+1],-y),(masks[i]^(1<<h),tuple(alt),y)]
    lev=[pool.id() for _ in range(m+2)];cross=[pool.id() for _ in slots];cl.append([-lev[0]])
    for i,z in enumerate(cross):
        a,b=lev[i:i+2];cl.extend([[-z,a,b],[-z,-a,-b],[z,-a,b],[z,a,-b]])
    cl.extend([[-a,-b] for a,b in zip(cross,cross[1:])])
    i=0;flipped=set()
    for a in word:
        if a==s:flipped.add(i)
        else:i+=1
    warm.extend(z if i in flipped else -z for i,z in enumerate(cross))
    if target>m:cl.extend(CardEnc.atleast(cross,bound=target-m,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    bins=defaultdict(list);ds={}
    for i,choices in enumerate(slots):
        for mask,f,h in choices:
            for omitted in [-1,*range(ng)]:
                other=mask if omitted<0 else mask^(1<<omitted)
                for j,frame,gate in bins.get(other,()):
                    if i-j<2:continue
                    clause=[-v for v in [h,gate] if v is not None]
                    for k,(a,b) in enumerate(zip(f,frame)):
                        if k==omitted or a==b:continue
                        key=tuple(sorted((a,b)))
                        if key not in ds:
                            v=pool.id();ds[key]=v;cl.extend([[-v,a,b],[-v,-a,-b]])
                        clause.append(ds[key])
                    if omitted<0:
                        if not clause:return 'UNSAT',None
                        cl.append(clause)
                    else:cl.extend([clause+[-cross[i]],clause+[-cross[j]],clause+[lev[i],lev[j]],clause+[-lev[i],-lev[j]]])
            bins[mask].append((i,f,h))
    with Cadical195(bootstrap_with=cl) as sat:
        sat.set_phases(warm);sat.conf_budget(cap);r=sat.solve_limited()
        if r!=True:return ('UNKNOWN' if r is None else 'UNSAT'),None
        model=set(sat.get_model())
    out=[]
    for i,choices in enumerate(slots):
        mask,f,_=next(row for row in choices if row[2] is None or row[2] in model)
        base=0
        for k,(a,b) in enumerate(pairs):
            v=int(f[k] in model);base|=(v<<a)|((v^((mask>>k)&1))<<b)
        out.append(base | (int(lev[i] in model)<<s))
        if cross[i] in model:out.append(base | (int(lev[i+1] in model)<<s))
    assert len(out)>target and valid(out)
    return 'FOUND',out

def main():
    n,tmax,seed,cap=map(int,sys.argv[1:]);rng=Random(seed)
    known=(ROOT/'q9_gap_generations/prior191.words').read_text().split()
    near=[w for w in (ROOT/'q9_via_q10/monotone_near.words').read_text().split() if len(w)==n]
    for t in range(tmax):
        w=list(map(int,rng.choice(near if near and t%2 else known)));axes=list(range(9));rng.shuffle(axes);s=axes.pop();g=list(zip(axes[::2],axes[1::2]))
        m=len(w)-w.count(s);sites=list(range(rng.randrange(2),m-1,2));sw=sorted(rng.sample(sites,rng.choice([4,9,18,len(sites)])))
        st,p=search(w,g,s,n,sw,cap);print(json.dumps(dict(trial=t,target=n,source=''.join(map(str,w)),pairs=g,sheet=s,swaps=sw,status=st,path=p)),flush=True)
        if p and n>=192:break
if __name__=='__main__':main()
