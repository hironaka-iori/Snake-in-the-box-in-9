"""Classify dense seven-cube forests by extending to half occupancy and marking deletions."""
from argparse import ArgumentParser
from collections import deque
from itertools import combinations
from math import comb
from pathlib import Path

from dense_eight import components, facet_completion
from solve import save

IDENTITY=bytes(range(256))
LOW=[sum(1<<v for v in range(128) if not (v>>j)&1) for j in range(7)]


def generators():
    base=bytes([v^1 if v<128 else v for v in range(256)])
    yield base,lambda x:((x&LOW[0])<<1)|((x&~LOW[0])>>1)
    for j in range(6):
        a,b=LOW[j]&~LOW[j+1],LOW[j+1]&~LOW[j]
        d=1<<j
        g=bytes([v^((3<<j) if v<128 and ((v>>j)^(v>>(j+1)))&1 else 0) for v in range(256)])
        yield g,lambda x,a=a,b=b,d=d:(x&~(a|b))|((x&a)>>d)|((x&b)<<d)


def invert(g):
    inv=bytearray(256)
    for v,w in enumerate(g):inv[w]=v
    return bytes(inv)


def full_classes(masks):
    gens=list(generators())
    used=set();classes=[]
    for root in sorted(masks):
        if root in used:continue
        trans={root:IDENTITY};q=deque([root])
        while q:
            m=q.popleft()
            for g,apply in gens:
                w=apply(m)
                if w not in trans:
                    trans[w]=trans[m].translate(g);q.append(w)
        assert set(trans).isdisjoint(used)
        used.update(trans)
        inv={m:invert(g) for m,g in trans.items()}
        stab={t.translate(g).translate(inv[apply(m)]) for m,t in trans.items() for g,apply in gens}
        stab.discard(IDENTITY)
        sites={v for v in range(128) if root>>v&1}
        assert all({g[v] for v in sites}==sites for g in stab)
        classes.append((sites,sorted(stab),len(trans)))
    assert len(used)==9424
    return classes


def valid_full(fixed):
    graph={v:{v^(1<<j) for j in range(7)}&fixed for v in fixed}
    if any(len(ns)>2 for ns in graph.values()):return False
    return all(e==len(part)-1 for e,part in components(fixed,7))


def classify(last):
    marked={}
    for n in range(64-last,65):
        rows=[]
        for line in Path(f"marked-seven-{n}.txt").read_text().splitlines():
            a,b,c,weight=map(int,line.split())
            mask=a|(b<<64)
            sites={x for x in range(128) if mask>>x&1}
            sub=components(sites,7)
            assert len(sites)==n and len(sub)==c and all(e==len(v)-1 for e,v in sub)
            rows.append((mask,weight))
        marked[n]=rows
    full=full_classes(m for m,w in marked[64])
    result={n:[] for n in marked}
    for fi,(sites,stab,weight) in enumerate(full):
        for t in range(last+1):
            seen=set()
            for deleted in combinations(sorted(sites),t):
                if deleted in seen:continue
                queue=deque([deleted]);seen.add(deleted);orbit=0
                while queue:
                    d=queue.popleft();orbit+=1
                    for g in stab:
                        w=tuple(sorted(g[v] for v in d))
                        if w not in seen:seen.add(w);queue.append(w)
                result[64-t].append(dict(full_class=fi,deleted=list(deleted),
                    forest=sorted(sites-set(deleted)),labelled=orbit*weight))
            assert len(seen)==comb(64,t)
    # A weight count alone would not prove unique completion. At each marked
    # forest enumerate all possible next sites and check every union explicitly.
    for n,marked_rows in marked.items():
        if n==64:continue
        for mask,_ in marked_rows:
            sites={x for x in range(128) if mask>>x&1}
            add={x for x in range(128) if x not in sites and valid_full(sites|{x})}
            assert len(add)==64-n and valid_full(sites|add)
        assert sum(weight for _,weight in marked_rows)==sum(r["labelled"] for r in result[n])
    return result


if __name__=="__main__":
    p=ArgumentParser();p.add_argument("--last",type=int,default=2)
    p.add_argument("--population",type=int);p.add_argument("--start",type=int,default=0)
    p.add_argument("--stop",type=int);p.add_argument("--budget",type=int,default=500000)
    p.add_argument("--checker",type=Path);p.add_argument("--deficits",action="store_true")
    p.add_argument("--skip-weight",action="store_true");a=p.parse_args()
    if a.population is None:
        rows=classify(a.last);save(Path("seven-deletion-classes.json"),rows)
        print({n:(len(v),sum(r["labelled"] for r in v)) for n,v in rows.items()})
    else:
        import json
        rows=json.loads(Path("seven-deletion-classes.json").read_bytes())[str(a.population)]
        for i in range(a.start,min(a.stop if a.stop is not None else len(rows),len(rows))):
            if a.skip_weight:
                source=Path(f"forest-role-weight-{a.population}-{i}.json")
                if source.exists() and json.loads(source.read_bytes())["max_edges"]<104:continue
            tag=f"dense8-class-{a.population}-{i}-{a.budget}"+("-deficit" if a.deficits else "")+("-checked" if a.checker else "")
            facet_completion(rows[i]["forest"],117,13,a.budget,tag,a.checker.resolve() if a.checker else None,a.deficits)
