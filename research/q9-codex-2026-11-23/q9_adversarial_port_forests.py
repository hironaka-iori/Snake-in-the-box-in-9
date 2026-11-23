"""Adversarial fixed-port families from tiled Q4 forests, independent of the 191 bank."""
import random,json,gzip
from q9_overlapping_port_bound import ROOT
from q9_port_edge_degree import solve
from q9_port_pattern_match import contained,patterns,axis

def forest(S):
    adj={v:[v^(1<<d) for d in range(4) if (v^(1<<d)) in S] for v in S}
    if any(len(n)>2 for n in adj.values()):return False
    todo=set(S)
    while todo:
        v=next(iter(todo));comp={v};stack=[v]
        while stack:
            w=stack.pop()
            for n in adj[w]:
                if n not in comp:comp.add(n);stack.append(n)
        if all(len(adj[u])==2 for u in comp):return False
        todo-=comp
    return True

def layouts():
    rng=random.Random(221050)
    q=set(range(16))
    masks=[]
    for m in range(1<<16):
        if m.bit_count()!=8 or not m&1:continue
        S={v for v in q if m>>v&1}
        if forest(S) and forest(q-S):masks.append(S)
    for i in range(24):
        while True:
            S=rng.choice(masks)
            planted={16*y+x for y in range(32) for x in (S if y.bit_count()%2==0 else q-S)}
            pools=[[(v,v^(1<<d)) for v in sorted(planted) if v<(v^(1<<d)) and (v^(1<<d)) in planted] for d in range(4)]
            directions=sorted(range(4),key=lambda d:-len(pools[d]))[:2]
            if min(len(pools[d]) for d in directions)>=25:break
        es=[]
        for d in directions:
            cand=pools[d].copy();rng.shuffle(cand)
            if i%3==1:cand.sort(key=lambda e:e[0]>>4)
            if i%3==2:cand.sort(key=lambda e:(e[0]>>4).bit_count())
            es+=cand[:25]
        yield es

if __name__=="__main__":
    from bound_q9_positive_ports import bound
    ps=patterns()
    with gzip.open(ROOT/"q9_adversarial_port_forests.jsonl.gz","wt") as f:
        for i,es in enumerate(layouts()):
            S={v for e in es for v in e}
            avoid=all(not contained(p,S) for p in ps)
            old=bound(S)
            if not avoid or old<221:
                row=dict(case=i,old=old,avoid=avoid,edges=es)
            else:
                b,d,w=solve(es);row=dict(case=i,old=old,avoid=avoid,edges=es,upper=b,den=d,weights=w)
            print(i,old,avoid,row.get("upper"),flush=True)
            f.write(json.dumps(row)+"\n")
