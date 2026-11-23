"""Complete one side of a parity cut, enumerating legal subsets of each free subcube."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
import json
from pysat.solvers import Minicard
from search_q9_free_record_slice import parents
from search_q9_wynn_plateau import NB
from verify_q9_center_avoidance import verify


def solve(seed,mask,offset,target,budget,control=False,at_least=False):
    fixed={v for v in seed if (v&mask).bit_count()%2==offset}
    delta=target+1-len(fixed)
    internal={v:sum(w in fixed for w in NB[v]) for v in fixed}
    assert all(d<=2 for d in internal.values())
    neighbors={}
    cubes={}
    for w in range(512):
        if (w&mask).bit_count()%2==offset:continue
        attached={v for v in NB[w] if v in fixed}
        if len(attached)>2 or any(internal[v]==2 for v in attached):continue
        neighbors[w]=attached
        cubes.setdefault(w&mask,[]).append(w)
    if delta>len(neighbors) or (delta<0 and not at_least):return "UNSAT",None
    with Minicard() as sat:
        def exactly(lits,k):
            if not 0<=k<=len(lits):sat.add_clause([]);return
            if k<len(lits):sat.add_atmost(lits,k)
            if k>0:sat.add_atmost([-x for x in lits],len(lits)-k)
        def small_eq(lits,k):
            if not 0<=k<=len(lits):sat.add_clause([]);return
            for c in combinations(lits,k+1):sat.add_clause([-x for x in c])
            for c in combinations(lits,len(lits)-k+1):sat.add_clause(list(c))
        tips=[]
        for v in fixed:
            if internal[v]==2:continue
            e=513+v;tips.append(e)
            small_eq([w+1 for w in NB[v] if w in neighbors]+[e],2-internal[v])
        next_id=1025
        forced_min=forced_max=0
        for group in cubes.values():
            assert len(group)<=8
            layouts=[]
            for bits in range(1<<len(group)):
                selected={w for i,w in enumerate(group) if bits>>i&1}
                ds={w:len(neighbors[w])+sum(v in selected for v in NB[w]) for w in selected}
                if any(d not in (1,2) for d in ds.values()) or list(ds.values()).count(1)>2:continue
                # Any cycle contained in this free group has no available exit.
                seen=set()
                bad=False
                for w in selected:
                    if w in seen:continue
                    comp=[w];seen.add(w)
                    for x in comp:
                        for y in NB[x]:
                            if y in selected and y not in seen:seen.add(y);comp.append(y)
                    if all(not neighbors[x] and ds[x]==2 for x in comp):bad=True;break
                if not bad:layouts.append((next_id,selected,{w for w,d in ds.items() if d==1}));next_id+=1
            if not layouts:return "UNSAT",None
            forced_min+=min(len(z[1]) for z in layouts);forced_max+=max(len(z[1]) for z in layouts)
            ids=[i for i,_,_ in layouts];exactly(ids,1)
            for w in group:
                for variable,k in [(1+w,1),(513+w,2)]:
                    pos=[row[0] for row in layouts if w in row[k]]
                    neg=[row[0] for row in layouts if w not in row[k]]
                    sat.add_clause([-variable,*pos]);sat.add_clause([variable,*neg])
                    if k==2 and pos:tips.append(variable)
        if forced_max<delta or (not at_least and delta<forced_min):return "UNSAT",None
        exactly(tips,2)
        if at_least:
            if delta>0:sat.add_atmost([-v-1 for v in neighbors],len(neighbors)-delta)
        else:exactly([v+1 for v in neighbors],delta)
        if not at_least and target%2==0:
            for e in tips:
                sat.add_clause([-e,next_id if (e-513).bit_count()%2 else -next_id])
        sat.set_phases([w+1 if w in seed else -w-1 for w in neighbors])
        hints=[w+1 for w in neighbors if w in seed] if control else []
        while True:
            cap=budget-sat.accum_stats()["conflicts"]
            if cap<=0:return "UNKNOWN",None
            sat.conf_budget(cap);ans=sat.solve_limited(assumptions=hints)
            if ans is not True:return ("UNKNOWN" if ans is None else "UNSAT"),None
            model=set(sat.get_model());picked=fixed|{w for w in neighbors if w+1 in model}
            ends=[v for v in picked if len(picked.intersection(NB[v]))==1]
            assert len(ends)==2 and len(picked)>=target+1 and (at_least or len(picked)==target+1)
            p=[ends[0]];unused=picked-set(p)
            while (nxt:=unused.intersection(NB[p[-1]])):
                assert len(nxt)==1
                w=nxt.pop();p.append(w);unused.remove(w)
            if not unused:
                verify(p);return "FOUND",p
            while unused:
                cycle=[unused.pop()]
                for v in cycle:
                    for w in NB[v]:
                        if w in unused:cycle.append(w);unused.remove(w)
                sat.add_clause([-w-1 for w in cycle if w not in fixed])


def init():
    global bank
    bank=parents()
    for p in bank:verify(p)

def work(job):
    i,mask,side,target,cap,at_least=job
    status,path=solve(bank[i],mask,side,target,cap,at_least=at_least)
    if path:
        assert len(path)>=target+1 and (at_least or len(path)==target+1)
        assert {v for v in path if (v&mask).bit_count()%2==side}=={v for v in bank[i] if (v&mask).bit_count()%2==side}
    return [i,mask,side,status,path]

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("ignored",type=int,choices=[1,2,3]);ap.add_argument("--parents",type=int,default=131)
    ap.add_argument("--budget",type=int,default=5500);ap.add_argument("--retry")
    ap.add_argument("--at-least",action="store_true")
    args=ap.parse_args();init()
    masks=[m for m in range(512) if m.bit_count()==9-args.ignored]
    for i in [0,19,40,80,130]:
        for offset in (0,1):
            st,w=solve(bank[i],masks[i%len(masks)],offset,191,10000,True,at_least=args.at_least)
            assert st=="FOUND" and len(w)==192
    if args.retry:
        jobs=[(i,m,s,192,args.budget,args.at_least) for i,m,s,st,w in map(json.loads,open(args.retry)) if st=="UNKNOWN"]
    else:
        jobs=[(i,m,s,192,args.budget,args.at_least) for i in range(args.parents) for m in masks for s in (0,1)]
    with ProcessPoolExecutor(4,initializer=init) as pool:
        for row in pool.map(work,jobs,chunksize=3):
            print(json.dumps(row,separators=(",",":")),flush=True)
            if row[-1]:break
