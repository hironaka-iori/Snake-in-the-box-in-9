"""Enumerate long Q8 paths whose vertices of one parity equal a prescribed set."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
LAST=HERE.parent/"253-repeated-segment-growth"
sys.path.insert(0,str(HERE.parent/"252-shorter-reference-segments"))
from replay_core import check_path, digest, word


def hamilton_orders(adjacency):
    n=len(adjacency)
    all_vertices=(1<<n)-1
    def follow(path,unseen):
        if not unseen:
            if path[0]<path[-1]:yield tuple(path)
            return
        moves=adjacency[path[-1]]&unseen
        if not moves:return
        # Removing the current endpoint from a Hamilton path leaves a connected path.
        reach=unseen & -unseen
        frontier=reach
        while frontier:
            first=frontier & -frontier
            frontier-=first
            new=adjacency[first.bit_length()-1] & unseen & ~reach
            frontier|=new
            reach|=new
        if unseen!=reach:return
        for i in bits(moves):
            path.append(i)
            yield from follow(path,unseen^(1<<i))
            path.pop()
    for i in range(n):yield from follow([i],all_vertices^(1<<i))


def bits(mask):
    while mask:
        low=mask&-mask
        yield low.bit_length()-1
        mask-=low


def catalogue(side):
    labels=defaultdict(list)
    for y in range(256):
        neighbours=tuple(i for i,x in enumerate(side) if (x^y).bit_count()==1)
        if 1<=len(neighbours)<=2:labels[neighbours].append(y)
    edges={key:vs for key,vs in labels.items() if len(key)==2}
    graph=[0]*len(side)
    for i,j in edges:
        graph[i]|=1<<j
        graph[j]|=1<<i
    orders=[]
    paths={}
    counts=Counter()
    for order in hamilton_orders(graph):
        orders.append(list(order))
        for vs in product(*(edges[tuple(sorted(pair))] for pair in zip(order,order[1:]))):
            mid=[side[order[0]]]
            for i,y in zip(order[1:],vs):mid.extend((y,side[i]))
            for prefix,suffix in product([None,*labels.get((order[0],),[])],
                                         [None,*labels.get((order[-1],),[])]):
                p=([prefix] if prefix is not None else [])+mid+([suffix] if suffix is not None else [])
                if not 96<=len(p)-1<=98:continue
                check_path(p)
                key=tuple(min(p,p[::-1]))
                if key in paths:raise ValueError("Repeated labelled path")
                paths[key]=sha256(word(p)).hexdigest();counts[len(p)-1]+=1
    return dict(side=side,orders=orders,internal_labels=[[*e,vs] for e,vs in sorted(edges.items())],
                singleton_labels=[[side[k[0]],v] for k,v in labels.items() if len(k)==1],
                labelled_lengths=counts,paths=[dict(vertices=list(p),shape=key) for p,key in sorted(paths.items())])


def main():
    source=LAST/"closure.json"
    old=json.loads(source.read_bytes())["paths"]
    focus={key:p for key,p in old.items() if key.startswith(("6f8ef24c","bac52b55"))}
    sides={}
    for key,p in focus.items():
        for offset in (0,1):sides.setdefault(tuple(sorted(p[offset::2])),[]).append([key,offset])
    if len(focus)!=2 or len(sides)!=3:raise ValueError("Reference class mismatch")
    rows=[]
    for side,origins in sides.items():
        result=catalogue(list(side))
        result["origins"]=origins;rows.append(result)
    shapes={r["shape"]:r["vertices"] for row in rows for r in row["paths"]}
    report=dict(sources={p.name:digest(p) for p in (Path(__file__),source,Path(sys.modules["replay_core"].__file__))},
                classes=rows,shapes=shapes,outside_previous=sorted(shapes.keys()-old.keys()))
    (HERE/"parity-families.json").write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    for row in rows:
        print(len(row["side"]),len(row["internal_labels"]),len(row["orders"]),row["labelled_lengths"])
    print("shapes",len(shapes),"outside closure",len(report["outside_previous"]))


if __name__=="__main__":main()
