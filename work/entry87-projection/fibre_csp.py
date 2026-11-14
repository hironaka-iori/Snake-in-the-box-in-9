"""Exact cube-fibre reconstruction after erasing any chosen coordinate set."""
import argparse, json
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver
from solve import BANK, BANK_HASH, defects, save, sha256


@lru_cache(None)
def fibre_patterns(d):
    size=1<<d; adj=[{v^(1<<b) for b in range(d)} for v in range(size)]
    patterns=[]
    def extend(q,used):
        patterns.append(tuple(q))
        for v in sorted(adj[q[-1]]-used):
            if adj[v]&used=={q[-1]}:extend(q+[v],used|{v})
    for v in range(size):extend([v],{v})
    return patterns,adj


def projected(q,axes):
    keep=[i for i in range(9) if i not in axes]; trace=[];pieces=[]
    def word(v,idx):return sum(((v>>b)&1)<<i for i,b in enumerate(idx))
    for v in q:
        w=word(v,keep)
        if not trace or w!=trace[-1]:trace.append(w);pieces.append([])
        pieces[-1].append(word(v,axes))
    shift=pieces[0][0]
    return trace,[tuple(v^shift for v in seg) for seg in pieces]


def solve_trace(trace,d,budget,target=193,phase_hint=None,seed=0):
    n=len(trace); size=1<<d; outside=9-d
    forms,adj=fibre_patterns(d); pool=IDPool()
    u=[[pool.id(("use",i,v)) for v in range(size)] for i in range(n)]
    heads=[[pool.id(("head",i,v)) for v in range(size)] for i in range(n)]
    tails=[[pool.id(("tail",i,v)) for v in range(size)] for i in range(n)]
    # A selector for each possible unoriented vertex set and oriented endpoints
    # could be large. The vertex degrees inside a tiny fibre already determine
    # the segment, and an induced-cycle exclusion removes every disconnected cycle.
    with Solver(name="cadical195") as sat:
        if seed:sat.configure({"seed":seed})
        def add(c):sat.add_clause(c)
        def exact_one(ls):
            add(ls)
            for a,b in combinations(ls,2):add([-a,-b])
        add([heads[0][0]])
        loc={}; edges=0; repeats=0
        # An isolated cycle component within a fibre would survive the local
        # degree equations. Enumerate the cycles by adding one closing site
        # to an induced path, then remove rotational duplicates.
        cycles=set()
        for q in forms:
            if len(q)<3:continue
            used=set(q)
            for v in adj[q[0]]&adj[q[-1]]-used:
                if adj[v]&used=={q[0],q[-1]}:cycles.add(tuple(sorted(used|{v})))
        for i,w in enumerate(trace):
            exact_one(heads[i]);exact_one(tails[i])
            for v in range(size):
                x=u[i][v];h=heads[i][v];t=tails[i][v]
                add([-h,x]);add([-t,x]);ns=[u[i][b] for b in sorted(adj[v])]
                # Every selected site's degree plus the number of marked tips
                # at the site is exactly two. Both tips may mark a singleton.
                lits=ns+[h,t]
                for triple in combinations(lits,3):add([-x,*[-y for y in triple]])
                for j in range(len(lits)):add([-x,*lits[:j],*lits[j+1:]])
            for c in cycles:add([-u[i][v] for v in c])
            if i:
                assert (trace[i-1]^w).bit_count()==1
                for v in range(size):
                    add([-heads[i][v],tails[i-1][v]]);add([heads[i][v],-tails[i-1][v]])
                    add([-u[i][v],-u[i-1][v],heads[i][v]])
            for j in loc.get(w,()):
                repeats+=1
                for v in range(size):
                    for y in adj[v]|{v}:add([-u[i][v],-u[j][y]])
            for b in range(outside):
                for j in loc.get(w^(1<<b),()):
                    if j==i-1:continue
                    edges+=1
                    for v in range(size):add([-u[i][v],-u[j][v]])
            loc.setdefault(w,[]).append(i)
        # At most 2^d occupied labels across all repeats of an address.
        # A single sequential cardinality bound counts every selected vertex.
        for c in CardEnc.atleast([v for row in u for v in row],bound=target,vpool=pool,encoding=EncType.cardnetwrk).clauses:add(c)
        if phase_hint is not None:
            phases=[]
            for i,piece in enumerate(phase_hint):
                for v in range(size):
                    phases.extend((u[i][v] if v in piece else -u[i][v],
                                   heads[i][v] if v==piece[0] else -heads[i][v],
                                   tails[i][v] if v==piece[-1] else -tails[i][v]))
            sat.set_phases(phases)
        sat.conf_budget(budget);yes=sat.solve_limited()
        row=dict(status="UNSAT" if yes is False else "OPEN" if yes is None else "FOUND",
                 visits=n,repeated_pairs=repeats,nonconsecutive_edges=edges,conflicts=sat.accum_stats()["conflicts"])
        if yes:
            pos=set(sat.get_model());out=[]
            for i,w in enumerate(trace):
                cell={v for v,x in enumerate(u[i]) if x in pos}
                head=next(v for v,x in enumerate(heads[i]) if x in pos)
                tail=next(v for v,x in enumerate(tails[i]) if x in pos)
                q=[head];cell.remove(head)
                while q[-1]!=tail:
                    follow=cell&adj[q[-1]];assert len(follow)==1
                    v=follow.pop();cell.remove(v);q.append(v)
                assert not cell
                out.extend(w|(v<<outside) for v in q)
            assert len(out)>=target and not defects(out)
            row.update(edges=len(out)-1,vertices=out)
        return row


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("dimension",type=int);p.add_argument("source",type=int);p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=20000);a=p.parse_args()
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH;q=json.loads(raw)[a.source]["vertex_sequence"]
    axes=list(combinations(range(9),a.dimension))
    # Prefer triples containing the two geometric coordinates of the old defect.
    axes.sort(key=lambda ss:(not {1,4}<=set(ss),ss))
    trace,_=projected(q,axes[a.first])
    assert solve_trace(trace,a.dimension,180000,192)["status"]=="FOUND"
    counts=[];file=Path(f"fibre-d{a.dimension}-{a.source}-{a.first}-{a.stop}-{a.budget}.json")
    for j in range(a.first,min(a.stop,len(axes))):
        combo=axes[j];trace,pieces=projected(q,combo)
        assert all(z in fibre_patterns(a.dimension)[0] for z in pieces)
        r=solve_trace(trace,a.dimension,a.budget);counts.append(dict(source=a.source,axes=combo,**r))
        save(file,counts);print(j,combo,r["status"],r["conflicts"],flush=True)
        if r["status"]=="FOUND":break
