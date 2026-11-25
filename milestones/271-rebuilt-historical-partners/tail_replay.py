"""Check complete free-tail cases by tracking occupied neighbours of each cube vertex."""
from collections import Counter

N=[[u^(1<<j) for j in range(8)] for u in range(256)]


def ceiling(parent, seed, keep, claimed):
    fixed=set(parent)
    occupied=set(seed[:keep+1])
    contacts=[sum(v in occupied for v in near) for near in N]
    longest=keep
    nodes=0
    def walk(tip,length):
        nonlocal longest,nodes
        nodes+=1
        if length>longest:
            longest=length
            assert length<=claimed
        for v in N[tip]:
            if v in occupied or v in fixed or contacts[v]!=1:continue
            occupied.add(v)
            for w in N[v]:contacts[w]+=1
            walk(v,length+1)
            for w in N[v]:contacts[w]-=1
            occupied.remove(v)
    walk(seed[keep],keep)
    assert longest==claimed
    return nodes


def audit_tails(roots,tails):
    counts=Counter()
    nodes=0
    certified=[]
    for k,series in tails["roots"].items():
        parent=roots[k]["parent"]
        for entry in series:
            seed=entry["start"]
            for row in entry["rounds"]:
                if not row["complete"]:continue
                keep=row["kept_partner_edges"]
                cap=row["joined_edges"]-len(parent)
                visits=ceiling(parent,seed,keep,cap)
                counts[len(seed)-1-keep]+=1
                nodes+=visits
                certified.append(dict(root=k,initial_edges=len(seed)-1,retained_edges=keep,
                                      maximum_partner_edges=cap,nodes=visits))
    return dict(complete_by_deleted_edges=counts,cases=certified,nodes=nodes)
