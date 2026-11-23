"""Fixed Q8 middle, two tip crossings, no restriction on either Q8 end segment."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import time
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

def middle(word):
    arm = [0]
    for d in word:
        arm.append(arm[-1] ^ (1<<int(d)))
    return arm

def valid(p):
    return len(set(p)) == len(p) and all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j,b in enumerate(p) if i<j)

def search(word, target, parity, engine, conflicts, warm=()):
    arm=middle(word)
    assert valid(arm)
    roots={arm[0], arm[-1]}
    free=sorted(set(range(256))-set(arm[1:-1]))
    allow=set(free)
    selected=lambda x:x+1
    end=lambda x:x+257
    clauses=[]
    pool=IDPool(start_from=513)
    solver=Solver(name=engine)
    def cardinal(ids,k):
        if k<0 or k>len(ids):
            clauses.append([])
            return
        clauses.extend(CardEnc.equals(ids,k,vpool=pool,encoding=EncType.totalizer).clauses)
    for x in free:
        nb=[selected(x^1<<i) for i in range(8) if (x^1<<i) in allow]
        s,e=selected(x),end(x)
        clauses.append([-e,s])
        if target%2==0 and ((x.bit_count()+1)&1)!=parity:
            clauses.append([-e])
        if x in roots:
            clauses.append([s]); clauses.append([e,*nb])
            for z in nb:clauses.append([-e,-z])
            clauses.extend([-u,-v] for u,v in combinations(nb,2))
        else:
            clauses.append([-s,*nb])
            for u in nb:clauses.append([-s,e,*(v for v in nb if v!=u)])
            clauses.extend([-e,-u,-v] for u,v in combinations(nb,2))
            clauses.extend([-s,-u,-v,-z] for u,v,z in combinations(nb,3))
        for i,j in combinations(range(8),2):
            if x & ((1<<i)|(1<<j)):continue
            square=[x,x^(1<<i),x^(1<<j),x^(1<<i)^(1<<j)]
            if all(v in allow for v in square):clauses.append([-selected(v) for v in square])
    cardinal([end(x) for x in free],2)
    for c in range(2):
        global_c=(target+1)//2+int(target%2==0 and c==parity)
        outside_need=global_c-sum(v.bit_count()%2==c for v in arm)
        cardinal([selected(x) for x in free if (x.bit_count()+1)%2==c],outside_need)
    solver.append_formula(clauses)
    if warm:solver.set_phases([selected(x) if x+256 in warm else -selected(x) for x in free])
    cuts=rounds=0
    start=time.monotonic()
    while True:
        left=conflicts-solver.accum_stats()['conflicts']
        if left<=0:status='UNKNOWN';break
        solver.conf_budget(left)
        outcome=solver.solve_limited()
        if outcome is not True:
            status='UNSAT' if outcome is False else 'UNKNOWN';break
        rounds+=1
        model=set(solver.get_model())
        active={x for x in free if selected(x) in model}
        full=set(arm)|{v+256 for v in active}
        graph={v:[v^1<<i for i in range(9) if (v^1<<i) in full] for v in full}
        assert len(full)==target+1 and all(1<=len(z)<=2 for z in graph.values())
        paths=[]; todo=set(full)
        while todo:
            component=set(); stack=[next(iter(todo))]
            while stack:
                v=stack.pop()
                if v in component:continue
                component.add(v);stack.extend(graph[v])
            todo-=component
            if all(len(graph[v])==2 for v in component):
                cut=[-selected(v-256) for v in component if v>=256]
                assert cut;solver.add_clause(cut);cuts+=1
            else:paths.append(component)
        assert len(paths)==1
        if len(paths[0])==len(full):
            p=[next(v for v in full if len(graph[v])==1)]
            while True:
                nxt=[z for z in graph[p[-1]] if len(p)==1 or z!=p[-2]]
                if not nxt:break
                p.append(nxt[0])
            assert valid(p) and len(p)==target+1
            status='FOUND';break
    result=dict(word=word,target=target,parity=parity,status=status,cycles_removed=cuts,models=rounds,seconds=round(time.monotonic()-start,4),conflicts=solver.accum_stats()['conflicts'])
    if status=='FOUND':result['path']=p
    solver.delete()
    return result

if __name__=='__main__':
    arg=argparse.ArgumentParser()
    arg.add_argument('words');arg.add_argument('--goal',type=int,default=192);arg.add_argument('--conflicts',type=int,default=3000)
    arg.add_argument('--engine',default='cadical195');arg.add_argument('--warm-control')
    opts=arg.parse_args()
    warm=tuple(map(int,Path(opts.warm_control).read_text().splitlines()[0].split()[5:])) if opts.warm_control else ()
    for w in Path(opts.words).read_text().split():
        for p in range(2 if opts.goal%2==0 else 1):
            print(json.dumps(search(w,opts.goal,p,opts.engine,opts.conflicts,warm)),flush=True)
