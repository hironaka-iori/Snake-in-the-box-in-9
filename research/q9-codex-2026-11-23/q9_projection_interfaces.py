"""Four-face projection with interface multiplicities and verified Q7 contact cuts."""
from collections import defaultdict
import itertools
import json

from verify_q9_free_dimension_cuts import edge7

INTERFACES = ((0, 1), (2, 3), (0, 2), (1, 3))
EDGE_INDEX = {frozenset(pair): i for i, pair in enumerate(INTERFACES)}
MOVES = {v: [(v^d, EDGE_INDEX[frozenset((v,v^d))]) for d in (1, 2)]
         for v in range(4)}


def compatible(edges, components, crossings):
    for (a,b), contact in zip(INTERFACES,crossings):
        if not contact:
            continue
        if edges[b] == 52:
            a,b = b,a
        if edges[a] != 52:
            continue
        if edges[b] >= 51:
            return False
        if contact >= 4 and edges[b] >= 50 and edges[b]+components[b] >= 54:
            return False
    return True


def profiles(max_crossings):
    states = {(0,(0,)*4)}
    for k in range(max_crossings+1):
        if k >= 17:
            for end, crossings in sorted(states):
                incidence = [int(v==0)+int(v==end) for v in range(4)]
                for (a,b), contact in zip(INTERFACES,crossings):
                    incidence[a] += contact
                    incidence[b] += contact
                assert all(n%2==0 for n in incidence)
                components = [n//2 for n in incidence]
                cap = [edge7(c) for c in components]
                target = 221-k
                spare = sum(cap)-target
                if spare < 0:
                    continue
                for deficits in itertools.product(*(range(min(e,spare)+1) for e in cap[:3])):
                    last = spare - sum(deficits)
                    if not 0 <= last <= cap[3]:
                        continue
                    edges = tuple(e-d for e,d in zip(cap,(*deficits,last)))
                    if compatible(edges,components,crossings):
                        yield k,end,crossings,edges,tuple(e+c for e,c in zip(edges,components))
        states = {(n, tuple(x+(j==i) for j,x in enumerate(crossings)))
                  for end,crossings in states for n,i in MOVES[end]}


def summarize(limit):
    stats = defaultdict(set)
    for k,end,crossings,edges,points in profiles(limit):
        stats[(k,end)].add((crossings,edges,points))
    out = []
    for (k,end), rows in sorted(stats.items()):
        out.append(dict(k=k,end=end,rows=len(rows),
                        axis_crossings=sorted({sum(r[0][:2]) for r in rows}),
                        point_ranges=list(zip(map(min,zip(*(r[2] for r in rows))),
                                              map(max,zip(*(r[2] for r in rows)))))))
    return out


if __name__=="__main__":
    for row in summarize(24):
        print(json.dumps(row))
