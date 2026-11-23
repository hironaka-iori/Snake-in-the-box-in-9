"""Lift four paired axis clocks and freely choose how often and where to cross the remaining axis."""
from collections import defaultdict, Counter
from itertools import combinations
from pathlib import Path
import argparse, random, json
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical195

ROOT=Path(__file__).resolve().parents[1]

def valid(p):
    return len(set(p))==len(p) and all(0<=x<512 for x in p) and all(((v^u).bit_count()==1)==(j==i+1) for j,v in enumerate(p) for i,u in enumerate(p[:j]))

def canonical(word):
    def normalize(seq):
        names={}
        return bytes(names.setdefault(a,len(names)) for a in seq)
    return min(normalize(word),normalize(reversed(word)))

def solve(word,pairs,sheet,target,cap,exclude=None,fixed=()):
    group={a:g for g,p in enumerate(pairs) for a in p}
    projected=[a for a in word if a!=sheet]
    m=len(projected)
    if target>2*m+1:return 'UNSAT',None
    pool=IDPool(); clauses=[]; phase=[]; mask=0
    clocks=[pool.id() for _ in pairs];clauses.extend([[-x] for x in clocks])
    frames=[tuple(clocks)];bucket=defaultdict(list);bucket[0].append(0)
    x=0;seen=set()
    for a in projected:
        g=group[a];x^=1<<a;mask^=1<<g;clocks[g]=pool.id()
        lit=clocks[g] if x & (1<<pairs[g][0]) else -clocks[g]
        phase.append(lit)
        if g in fixed or g not in seen:seen.add(g);clauses.append([lit])
        frames.append(tuple(clocks));bucket[mask].append(len(frames)-1)
    level=[pool.id() for _ in range(m+2)];clauses.append([-level[0]])
    cross=[pool.id() for _ in frames]
    def unequal(a,b,z):
        return [[-z,a,b],[-z,-a,-b],[z,-a,b],[z,a,-b]]
    for i,z in enumerate(cross):clauses.extend(unequal(level[i],level[i+1],z))
    for a,b in zip(cross,cross[1:]):clauses.append([-a,-b])
    i=0;old=set()
    for a in word:
        if a==sheet:old.add(i)
        else:i+=1
    phase.extend(z if i in old else -z for i,z in enumerate(cross))
    need=max(0,target-m)
    if need:clauses.extend(CardEnc.atleast(cross,bound=need,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    diffs={}
    for mask,sites in bucket.items():
        for omitted in [-1,*range(len(pairs))]:
            other=mask if omitted<0 else mask^(1<<omitted)
            if other<mask:continue
            for i in sites:
                for j in bucket.get(other,()):
                    if abs(i-j)<=1 or (other==mask and j<i):continue
                    choices=[]
                    for g,(a,b) in enumerate(zip(frames[i],frames[j])):
                        if g==omitted or a==b:continue
                        k=tuple(sorted((a,b)))
                        if k not in diffs:
                            z=pool.id();diffs[k]=z;clauses.extend([[-z,a,b],[-z,-a,-b]])
                        choices.append(diffs[k])
                    if omitted<0:
                        if not choices:return 'UNSAT',None
                        clauses.append(choices)
                    else:
                        clauses.extend([choices+[-cross[i]],choices+[-cross[j]],choices+[level[i],level[j]],choices+[-level[i],-level[j]]])
    with Cadical195(bootstrap_with=clauses) as s:
        s.set_phases(phase)
        while True:
            remaining=cap-s.accum_stats()['conflicts']
            if remaining<=0:return 'UNKNOWN',None
            s.conf_budget(remaining);r=s.solve_limited()
            if r!=True:return ('UNKNOWN' if r is None else 'UNSAT'),None
            model=set(s.get_model())
            p=[];base=0
            for i,frame in enumerate(frames):
                if i:
                    g=group[projected[i-1]]
                    axis=pairs[g][0 if ((frame[g] in model)!=(frames[i-1][g] in model)) else 1]
                    base^=1<<axis
                p.append(base | (int(level[i] in model)<<sheet))
                if cross[i] in model:p.append(base | (int(level[i+1] in model)<<sheet))
            assert len(p)>target and valid(p)
            steps=[(x^y).bit_length()-1 for x,y in zip(p,p[1:])]
            if not exclude or canonical(steps) not in exclude:return 'FOUND',p
            primary=set(cross).union(*(set(row) for row in frames))
            s.add_clause([-v if v in model else v for v in primary])


def run():
    ap=argparse.ArgumentParser()
    for field in ['goal','trials','seed','cap']:ap.add_argument(field,type=int)
    opt=ap.parse_args();rng=random.Random(opt.seed)
    wb=(ROOT/'q9_gap_generations/prior191.words').read_text().split()
    near=(ROOT/'q9_via_q10/monotone_near.words').read_text().split()
    stats=Counter()
    for trial in range(opt.trials):
        source=rng.choice(wb if trial%3 or opt.goal<192 else near)
        word=list(map(int,source));ds=list(range(9));rng.shuffle(ds);sheet=ds.pop();pairs=list(zip(ds[::2],ds[1::2]))
        st,p=solve(word,pairs,sheet,opt.goal,opt.cap);stats[st]+=1
        print(json.dumps(dict(trial=trial,status=st,target=opt.goal,sheet=sheet,pairs=pairs,source=source,path=p),separators=(',',':')),flush=True)
        if st=='FOUND' and opt.goal>=192:break
    print(json.dumps(dict(done=True,counts=stats)),flush=True)
if __name__=='__main__':run()
