"""Glue two rooted Q8 paths by choosing their even anchors and odd witnesses."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
from paired_seeds import extract
from solve import defects,save


def skeleton(anchors):
    active=set(anchors);adj={v:set() for v in active};edge={};tip={}
    for w in range(256):
        if w.bit_count()%2==0:continue
        n=tuple(sorted(active.intersection(w^(1<<b) for b in range(8))))
        if len(n)==1:tip.setdefault(n[0],[]).append(w)
        if len(n)==2:
            x,y=n;adj[x].add(y);adj[y].add(x);edge.setdefault(n,[]).append(w)
    return adj,edge,tip


@lru_cache(maxsize=50000)
def orders(anchors,cap):
    adj,edge,tip=skeleton(anchors)
    order=[0];free=set(anchors)-{0};out=[]
    def visit(v):
        if not free:
            if cap and v not in tip:return
            lists=[tuple(edge[tuple(sorted(k))]) for k in zip(order,order[1:])]
            if cap:lists.append(tuple(tip[v]))
            out.append((tuple(order),tuple(lists)))
            return
        if not adj[v]&free:return
        # A completion visits the residual set from v and has at most one
        # other endpoint. A degree-one residual anchor must be that endpoint.
        leaves=0
        for y in free:
            d=len(adj[y]&free)+(v in adj[y])
            if d==0:return
            if d==1:
                leaves+=1
                if leaves>1 or (cap and y not in tip):return
        for y in sorted(adj[v]&free):
            order.append(y);free.remove(y);visit(y);free.add(y);order.pop()
    visit(0)
    return tuple(out)


def representatives(lists):
    # One global matching chooses mutually distinct odd addresses for both
    # faces. Options belonging to cubes in one face are already disjoint.
    owner={}
    def augment(i,seen):
        for w in lists[i]:
            if w in seen:continue
            seen.add(w)
            if w not in owner or augment(owner[w],seen):
                owner[w]=i;return True
        return False
    for i in sorted(range(len(lists)),key=lambda j:len(lists[j])):
        if not augment(i,set()):return None
    choice=[0]*len(lists)
    for w,i in owner.items():choice[i]=w
    assert len(set(choice))==len(choice) and all(v in ls for v,ls in zip(choice,lists))
    return choice


def assemble(order,chosen):
    q=[]
    for i,x in enumerate(order):
        q.append(x)
        if i<len(chosen):q.append(chosen[i])
    return q


def test(A,B,cap,stats):
    if set(A)&set(B)!={0}:stats["anchor overlap"]+=1;return None
    cases=[orders(tuple(sorted(anchors)),s==cap) for s,anchors in enumerate((A,B))]
    if any(not item for item in cases):
        stats["no rooted order"]+=1;return None
    stats["both have an order"]+=1
    for (left,la),(right,lb) in product(*cases):
        stats["order pairs"]+=1
        choice=representatives(la+lb)
        if choice is None:continue
        q=assemble(left,choice[:len(la)])[::-1]+[w|256 for w in assemble(right,choice[len(la):])]
        assert len(q)==(192 if cap is None else 193) and not defects(q)
        return q
    stats["no joint matching"]+=1
    return None


def options(base,other):
    # When only one face is edited the other anchor set remains fixed.
    for x in sorted(base-{0}):
        for y in range(256):
            if y.bit_count()%2==0 and y not in base|other:
                yield sorted((base-{x})|{y}),[x,y]


def run(a):
    seeds=extract();rows=[]
    for i in range(a.start,a.stop):
        rec=seeds[i];A=set(rec["parent"][::2]);B=set(rec["known_partner"][::2])
        assert len(A)==49 and len(B)==48
        assert test(A,B,None,Counter()) is not None
        for cap in (0,1):
            stats=Counter();w=test(A,B,cap,stats)
            hit=None
            if a.radius and not w:
                for side in (0,1):
                    sets=[A,B]
                    for fresh,edit in options(sets[side],sets[1-side]):
                        first,second=(fresh,B) if side==0 else (A,fresh)
                        w=test(first,second,cap,stats)
                        if w:
                            hit=[side,*edit];break
                    if w:break
            rows.append(dict(index=i,cap=cap,stats=stats,change=hit,witness=w))
            if w:print("WITNESS",i,cap,hit,flush=True);break
        if w:break
    save(Path(f"joint-parity-{a.radius}-{a.start}-{a.stop}.json"),rows)
    print(len(rows),sum((Counter(r["stats"]) for r in rows),Counter()),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    for name in ("start","stop","radius"):parser.add_argument(name,type=int)
    run(parser.parse_args())
