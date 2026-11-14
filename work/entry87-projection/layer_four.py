"""Construct a 192-edge snake from four arbitrary Q7 paths in Gray-ordered layers."""
import argparse,json
from collections import Counter
from itertools import combinations
from pathlib import Path
from ortools.sat.python import cp_model
from solve import save,defects


def find(dim,sizes,seconds,seed,hint=None,radius=None,flexible=False,desired=None):
    size=1<<dim;order=[0,1,3,2];model=cp_model.CpModel()
    target=desired if desired is not None else sum(sizes)
    x={(l,v):model.new_bool_var(f"x{l}_{v}") for l in range(4) for v in range(size)}
    end={(l,v):model.new_bool_var(f"e{l}_{v}") for l in range(4) for v in range(size)}
    # The first cross can be translated to address zero. The inner-coordinate
    # permutation group can place the second cross at a prefix of one's bits.
    sites=[[0],[(1<<i)-1 for i in range(1,dim+1)],list(range(size))]
    joints=[]
    for j,(l,r) in enumerate(zip(order,order[1:])):
        flags={}
        for v in range(size):
            if v not in sites[j]:
                model.add(x[l,v]+x[r,v]<=1);continue
            h=model.new_bool_var(f"join{j}_{v}");flags[v]=h
            model.add(h<=x[l,v]);model.add(h<=x[r,v]);model.add(h>=x[l,v]+x[r,v]-1)
        model.add_exactly_one(flags.values());joints.append(flags)
    for v in range(size):model.add(x[0,v]+x[2,v]<=1)
    for idx,l in enumerate(order):
        selected=sum(x[l,v] for v in range(size))
        if flexible:
            if dim==7:model.add(selected<=51)
            model.add(selected>=2)
        else:model.add(selected==sizes[idx])
        model.add(sum(end[l,v] for v in range(size))==2)
        if idx:
            for v,h in joints[idx-1].items():model.add(end[l,v]>=h)
        if idx<3:
            for v,h in joints[idx].items():model.add(end[l,v]>=h)
        if 0<idx<3:
            for v in joints[idx-1].keys() & joints[idx].keys():model.add(joints[idx-1][v]+joints[idx][v]<=1)
        for v in range(size):
            ns=[x[l,v^(1<<b)] for b in range(dim)]
            model.add(end[l,v]<=x[l,v])
            model.add(sum(ns)==2-end[l,v]).only_enforce_if(x[l,v])
            for b in range(dim):
                for a in range(b):
                    mask=1<<a|1<<b
                    if not v&mask:model.add(x[l,v]+x[l,v^(1<<a)]+x[l,v^(1<<b)]+x[l,v^mask]<=3)
    # Address parity alternates on each of the four internal paths.
    for idx,l in enumerate(order):
        even=[x[l,v] for v in range(size) if v.bit_count()%2==0]
        even_ends=[end[l,v] for v in range(size) if v.bit_count()%2==0]
        # If both ends are even, there is one extra even vertex; if both are
        # odd, one fewer. Opposite endpoint colours give equal classes.
        n=sum(x[l,v] for v in range(size)) if flexible else sizes[idx]
        model.add(2*sum(even)==n+sum(even_ends)-1)
    model.add(sum(x.values())==target)
    if hint:
        for (l,v),var in x.items():model.add_hint(var,int(v in hint[l]))
        if radius is not None:
            for l in order:model.add(sum(1-x[l,v] for v in hint[l])<=radius)
    solver=cp_model.CpSolver();solver.parameters.max_time_in_seconds=seconds
    solver.parameters.num_search_workers=1;solver.parameters.random_seed=seed
    cuts=[];status="OPEN";witness=None;branches=conflicts=0
    import time
    start=time.monotonic()
    while (left:=seconds-(time.monotonic()-start))>0:
        solver.parameters.max_time_in_seconds=left;result=solver.solve(model)
        branches+=solver.num_branches;conflicts+=solver.num_conflicts
        if result not in (cp_model.OPTIMAL,cp_model.FEASIBLE):
            status="UNSAT" if result==cp_model.INFEASIBLE else "OPEN";break
        full={v|(l<<dim) for (l,v),var in x.items() if solver.value(var)}
        graph={v:{v^(1<<b) for b in range(dim+2)}&full for v in full}
        tips=[v for v,ns in graph.items() if len(ns)==1];assert len(tips)==2
        q=[tips[0]];unseen=full-set(q)
        while (nxt:=graph[q[-1]]&unseen):
            v=nxt.pop();q.append(v);unseen.remove(v)
        if not unseen:
            assert len(q)==target and not defects(q)
            if q[0]>>dim==2:q.reverse()
            status="FOUND";witness=q;break
        while unseen:
            v=unseen.pop();component={v};stack=[v]
            while stack:
                fresh=graph[stack.pop()]&unseen;unseen-=fresh;stack.extend(fresh);component|=fresh
            assert all(len(graph[v]&component)==2 for v in component)
            cuts.append(sorted(component));model.add(sum(x[v>>dim,v&(size-1)] for v in component)<len(component))
    return dict(dim=dim,layer_sizes=sizes,flexible=flexible,target=target,status=status,seconds=seconds,seed=seed,cuts=cuts,
                branches=branches,conflicts=conflicts,witness=witness)


def normalized_hint(q):
    trans=[i for i,(x,y) in enumerate(zip(q,q[1:])) if x>>7!=y>>7]
    assert len(trans)==3 and [q[0]>>7,*[q[i+1]>>7 for i in trans]]==[0,1,3,2]
    first=q[trans[0]]&127; second=(q[trans[1]]&127)^first
    bits=sorted(range(7),key=lambda b:not (second>>b&1))
    hints=[set() for _ in range(4)]
    for v in q:
        raw=(v&127)^first
        hints[v>>7].add(sum(((raw>>b)&1)<<i for i,b in enumerate(bits)))
    return hints


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("sizes",type=int,nargs=4);p.add_argument("--dim",type=int,default=7)
    p.add_argument("--seconds",type=int,default=120);p.add_argument("--seed",type=int,default=71);a=p.parse_args()
    # Smaller cube constructive control exercises the joint and degree equations.
    assert find(4,[3,3,3,3],10,1)["status"]=="FOUND"
    r=find(a.dim,a.sizes,a.seconds,a.seed);save(Path(f"four-layers-{a.dim}-{'-'.join(map(str,a.sizes))}-{a.seconds}-{a.seed}.json"),r)
    print(r["status"],r["branches"],r["conflicts"],flush=True)
