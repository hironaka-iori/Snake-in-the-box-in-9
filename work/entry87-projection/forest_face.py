"""Complement a fixed induced forest in a whole Q8 face, with all legal crossings free."""
import argparse,json
from collections import Counter
from itertools import combinations,permutations,product
from pathlib import Path
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from fixed_face import cycle_types
from export_drat import checked_export
from solve import BANK,BANK_HASH,sha256,defects,save


def canonical(components):
    def orient(c,f):return c[::-1] if f else c
    best=None
    # Length-first ordering removes unequal-sized component permutations,
    # while equal lengths can be swapped. The preordered roots fix translation.
    lengths=sorted(map(len,components),reverse=True)
    for order in permutations(components):
        if list(map(len,order))!=lengths:continue
        for flags in product((0,1),repeat=len(order)):
            paths=[orient(c,r) for c,r in zip(order,flags)];names={};origin=paths[0][0]
            for path in paths:
                for v,w in zip(path,path[1:]):
                    bit=(v^w).bit_length()-1;names.setdefault(bit,len(names))
            unused=[i for i in range(8) if i not in names]
            for perm in permutations(unused):
                labels=names.copy()
                for b in perm:labels[b]=len(labels)
                def map_v(v):return sum(((v^origin)>>i&1)<<j for i,j in labels.items())
                key=tuple(tuple(map_v(v) for v in c) for c in paths)
                if best is None or key<best:best=key
    return best


def records():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    bank=json.loads(raw);cases={}
    for index,r in enumerate(bank):
        q=r["vertex_sequence"];mv=[(a^b).bit_length()-1 for a,b in zip(q,q[1:])]
        freq=Counter(mv);minimum=min(freq.values())
        for axis,n in freq.items():
            if n!=minimum or n not in (2,3,4):continue
            split=[j for j,b in enumerate(mv) if b==axis]
            cuts=[0]+[j+1 for j in split]+[len(q)]
            def drop(v):return (v&((1<<axis)-1))|((v>>(axis+1))<<axis)
            runs=[[drop(v) for v in q[a:b]] for a,b in zip(cuts,cuts[1:])]
            for side in (0,1):
                parts=runs[side::2]
                if len(parts)<2:continue
                key=canonical(parts)
                if key not in cases:cases[key]=dict(components=key,occurrences=[])
                cases[key]["occurrences"].append(dict(entry=index,axis=axis,minimum=minimum,side=side))
    return list(cases.values())


def solve(r,i,budget,checker,desired=193):
    parts=r["components"];P=set().union(*map(set,parts))
    pg={v:{v^(1<<j) for j in range(8)}&P for v in P}
    assert sum(map(len,parts))==len(P) and all(not defects(c) for c in parts)
    assert sum(map(len,pg.values()))==2*(len(P)-len(parts)) and all(len(g) in (1,2) for g in pg.values())
    roots={v for v,ns in pg.items() if len(ns)==1};assert len(roots)==2*len(parts)
    allowed=set(range(256))-(P-roots);target=desired-len(P)
    graph={v:sorted({v^(1<<b) for b in range(8)}&allowed) for v in sorted(allowed)}
    pool=IDPool();use={v:pool.id(("select",v)) for v in graph};end={v:pool.id(("end",v)) for v in graph}
    clauses=[];extra=[];witness=None;tag=f"{i}-{desired}"
    with Solver(name="cadical195",with_proof=checker is not None) as sat:
        def add(c):
            sat.add_clause(c)
            if checker:clauses.append(c)
        def eq(ls,k):
            for c in CardEnc.equals(ls,bound=k,vpool=pool,encoding=EncType.totalizer).clauses:add(c)
        eq(list(use.values()),target)
        eq([*end.values(),*[-use[v] for v in sorted(roots)]],2)
        for path in parts:add([use[path[0]],use[path[-1]]])
        # The total Q9 parity counts differ by one for an odd cardinality
        # and agree for even cardinality. The upper face reverses address parity.
        many=(desired+1)//2;few=desired//2
        phase=pool.id("even_major")
        low_even=sum(v.bit_count()%2==0 for v in P)
        odd_upper=[use[v] for v in graph if v.bit_count()%2==1]
        if many==few:eq(odd_upper,many-low_even)
        else:
            for parity,n in ((0,few),(1,many)):
                if not 0<=n-low_even<=len(odd_upper):
                    add([phase] if parity==0 else [-phase]);continue
                for c in CardEnc.equals(odd_upper,bound=n-low_even,vpool=pool,encoding=EncType.totalizer).clauses:
                    add(([phase] if parity==0 else [-phase])+c)
            for v in graph:
                literal=phase if v.bit_count()%2 else -phase
                add([-end[v],literal])
            for v in sorted(roots):
                literal=-phase if v.bit_count()%2 else phase
                add([use[v],literal])
        for v,adj in graph.items():
            x=use[v];e=end[v];ls=[use[w] for w in adj];add([-e,x])
            if v in roots:
                add([-x,e,*ls])
                for y in ls:add([-e,-y])
                for a,b in combinations(ls,2):add([-x,-a,-b])
            else:
                add([-x,*ls])
                for a,b,c in combinations(ls,3):add([-x,-a,-b,-c])
                for a,b in combinations(ls,2):add([-e,-a,-b])
                for j in range(len(ls)):add([-x,e,*ls[:j],*ls[j+1:]])
        cycles=set()
        for d in (2,3,4):
            for axes in combinations(range(8),d):
                mask=sum(1<<j for j in axes)
                spread=[sum(((v>>k)&1)<<b for k,b in enumerate(axes)) for v in range(1<<d)]
                for base in range(256):
                    if base&mask:continue
                    for cyc in cycle_types[d]:
                        C=tuple(sorted(base|spread[v] for v in cyc))
                        if C in cycles or not set(C)<=allowed:continue
                        assert all(len(set(graph[v])&set(C))==2 for v in C)
                        cycles.add(C);add([-use[v] for v in C])
        status="OPEN"
        while True:
            remain=budget-sat.accum_stats()["conflicts"]
            if remain<=0:break
            sat.conf_budget(remain);ans=sat.solve_limited()
            if ans is not True:
                status="UNSAT" if ans is False else "OPEN";break
            pos=set(sat.get_model());full=P|{v|256 for v in graph if use[v] in pos}
            adj={v:{v^(1<<b) for b in range(9)}&full for v in full}
            ends=[v for v,g in adj.items() if len(g)==1]
            assert len(full)==desired and len(ends)==2 and all(len(g) in (1,2) for g in adj.values())
            q=[ends[0]];used=set(q)
            while adj[q[-1]]-used:
                y=(adj[q[-1]]-used).pop();q.append(y);used.add(y)
            if len(q)==desired:
                assert not defects(q);witness=q;status="FOUND";break
            rest=full-used
            while rest:
                v=rest.pop();component={v};todo=[v]
                while todo:
                    a=adj[todo.pop()]&rest;rest-=a;component|=a;todo.extend(a)
                assert all(len(adj[v]&component)==2 for v in component)
                cut=sorted(v^256 for v in component if v>=256);assert cut
                extra.append(cut);add([-use[v] for v in cut])
        out=dict(index=i,desired=desired,components=parts,source=r["occurrences"],
                 target=target,status=status,stats=sat.accum_stats(),cycles=len(cycles),dynamic=extra,witness=witness)
        if checker and status=="UNSAT":out.update(checked_export(sat,clauses,Path("forest-face-proof-"+tag),checker))
    save(Path("forest-face-"+tag+("-checked" if checker else "")+".json"),out)
    print(i,[len(c) for c in parts],target,status,out["stats"]["conflicts"],flush=True)


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--index",type=int);p.add_argument("--budget",type=int,default=350000)
    p.add_argument("--checker",type=Path);p.add_argument("--desired",type=int,default=193);a=p.parse_args()
    rs=records()
    if a.index is None:
        save(Path("forest-faces.json"),rs)
        print(len(rs),Counter((len(r["components"]),sum(map(len,r["components"]))) for r in rs))
    else:solve(rs[a.index],a.index,a.budget,a.checker.resolve() if a.checker else None,a.desired)
