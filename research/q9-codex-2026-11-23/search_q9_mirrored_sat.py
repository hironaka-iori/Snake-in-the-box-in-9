"""Complete a partly specified Q9 snake symmetric about its central vertex or edge."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import random

from pysat.solvers import Minicard
from search_q9_wynn_plateau import NB, verify


def mirror(x, pairs, edge=False):
    for i in range(0, 2*pairs, 2):
        if ((x>>i)^(x>>(i+1))) & 1:
            x ^= 3 << i
    return x ^ (256 if edge else 0)


def graph(pairs, edge=False):
    vertices = {0} | {x for x in range(512) if x < mirror(x, pairs, edge) and
                      (not edge or (x ^ mirror(x,pairs,edge)).bit_count()>1)}
    adj = {v:set() for v in vertices}
    conflict = {v:set() for v in vertices}
    for v in vertices:
        for w in NB[v]:
            rep = min(w, mirror(w, pairs, edge))
            if rep not in vertices or rep == v:
                continue
            if v and rep and mirror(w, pairs, edge) in NB[v]:
                conflict[v].add(rep)
            else:
                adj[v].add(rep)
    assert all(v in adj[w] for v in vertices for w in adj[v])
    return vertices, adj, conflict


def lift(path, pairs, edge=False):
    real = [0]
    for v in path[1:]:
        real.append(next(w for w in (v, mirror(v,pairs,edge)) if w in NB[real[-1]]))
    result = [mirror(v,pairs,edge) for v in reversed(real if edge else real[1:])] + real
    assert verify(result)
    return result


def solve(g, anchor, seed, length, budget, pairs, edge=False, change=False):
    vertices, adj, conflict = g
    fixed_degree = {v:len(adj[v]&anchor) for v in vertices}
    if any(conflict[v]&anchor or fixed_degree[v]>(1 if v==0 else 2) for v in anchor):
        return "UNSAT",None
    saturated = {v for v in anchor if fixed_degree[v]==(1 if v==0 else 2)}
    free = {v for v in vertices-anchor if not conflict[v]&anchor and
            not adj[v]&saturated and fixed_degree[v]<=2}
    with Minicard() as s:
        def exact(lits, k):
            if not 0<=k<=len(lits):
                s.add_clause([])
            else:
                s.add_atmost(lits,k)
                s.add_atmost([-x for x in lits],len(lits)-k)
        if edge:
            exact([v+1 for v in free], length+1-len(anchor))
        for color in (() if edge else (0,1)):
            need=(length+2-color)//2-sum(v.bit_count()%2==color for v in anchor)
            exact([v+1 for v in free if v.bit_count()%2==color],need)
        if change:
            s.add_clause([-v-1 for v in free & seed])
        endvars=[]
        for v in free:
            for w in free & conflict[v]:
                if w>v:
                    s.add_clause([-v-1,-w-1])
        for v in anchor|free:
            if v in saturated:
                continue
            guard=[] if v in anchor else [-v-1]
            adjl=[w+1 for w in adj[v]&free]
            required=(1 if v==0 else 2)-fixed_degree[v]
            if v and (edge or v.bit_count()%2==length%2):
                end=v+513
                endvars.append(end)
                adjl.append(end)
                if guard:
                    s.add_clause([-end,v+1])
            if len(adjl)<required:
                s.add_clause(guard)
                continue
            for c in combinations(adjl,required+1):
                s.add_clause(guard+[-x for x in c])
            for c in combinations(adjl,len(adjl)-required+1):
                s.add_clause(guard+list(c))
        exact(endvars,1)
        s.set_phases([v+1 if v in seed else -v-1 for v in free])
        while True:
            remain=budget-s.accum_stats()["conflicts"]
            if remain<=0:
                return "UNKNOWN",None
            s.conf_budget(remain)
            ok=s.solve_limited()
            if ok is not True:
                return ("UNSAT" if ok is False else "UNKNOWN"),None
            model=set(s.get_model())
            chosen=anchor|{v for v in free if v+1 in model}
            path=[0]
            unused=chosen-{0}
            while adj[path[-1]]&unused:
                nxt,=adj[path[-1]]&unused
                unused.remove(nxt)
                path.append(nxt)
            if not unused:
                assert len(path)==length+1
                return "FOUND",lift(path,pairs,edge)
            while unused:
                comp=[unused.pop()]
                for v in comp:
                    for w in adj[v]&unused:
                        unused.remove(w)
                        comp.append(w)
                c=set(comp)
                border={w+1 for v in c for w in (adj[v]&free)-c}
                if not anchor&c:
                    border.add(-min(c)-1)
                s.add_clause(list(border))


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("beam_output",type=Path)
    ap.add_argument("--runs",type=int,default=1200)
    ap.add_argument("--budget",type=int,default=12000)
    ap.add_argument("--target",type=int,default=192)
    ap.add_argument("--seed",type=int,default=2619)
    ap.add_argument("--climb",action="store_true")
    ap.add_argument("--center-edge",action="store_true")
    ap.add_argument("--walk",action="store_true",help="alternate same-length repairs with extensions")
    a=ap.parse_args()
    if a.target%2 != int(a.center_edge):
        ap.error("target parity must match the center type")
    rng=random.Random(a.seed)
    seeds=[]
    for line in a.beam_output.read_text().splitlines():
        if line.startswith("HALF "):
            _,t,*p=line.split()
            pairs = int(t)
            seeds.append((pairs,[min(v,mirror(v,pairs,a.center_edge)) for v in map(int,p)]))
    if not seeds:
        ap.error("missing HALF records")
    graphs={t:graph(t,a.center_edge) for t,_ in seeds}
    for t,p in seeds:
        lift(p,t,a.center_edge)
    best=max(len(p)-1 for _,p in seeds)
    if a.walk:
        seeds=[(t,p) for t,p in seeds if len(p)-1==best]
    for i in range(a.runs):
        t,p=rng.choice(seeds[-6:])
        fixed={0}|set(rng.sample(p[1:],rng.randint(len(p)//3,4*len(p)//5)))
        want=min(best+1,a.target//2) if a.climb and i%4 else a.target//2
        neutral = a.walk and i%5 in (1,2,3)
        if neutral:
            want=len(p)-1
        status,w=solve(graphs[t],fixed,set(p),want,a.budget,t,a.center_edge,neutral)
        print(json.dumps(dict(run=i,k=len(fixed),half_goal=want,status=status,vertices=w)),flush=True)
        if w:
            if len(w)-1>=a.target:
                return
            if a.walk and want>best:
                seeds.clear()
            best=max(best,want)
            seeds.append((t,[min(v,mirror(v,t,a.center_edge)) for v in w[want+int(a.center_edge):]]))


if __name__=="__main__":
    main()
