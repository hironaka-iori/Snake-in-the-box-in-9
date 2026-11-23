"""Locate every cube-isometric copy of the 66 anchors, including chains that cross a chord."""
from pathlib import Path
from collections import Counter
from itertools import permutations
import json
from match_q9_anchor_obstruction import longest_component,labels

def images_in_graph(vertices,chain,anchors):
    neighbors={v:{d for d in range(9) if (v^(1<<d)) in vertices} for v in vertices}
    word=labels(chain)
    out=set()
    def walk(origin,v,idx,perm):
        if idx==len(word):
            unused=sorted(set(range(9))-perm.keys())
            for target in permutations(set(range(9))-set(perm.values())):
                mapping=perm|dict(zip(unused,target))
                pts=frozenset(origin^sum(1<<j for i,j in mapping.items() if (a^chain[0])&(1<<i)) for a in anchors)
                if pts<=vertices:out.add(pts)
            return
        axis=word[idx]
        if axis in perm:
            d=perm[axis]
            if d in neighbors[v]:
                walk(origin,v^(1<<d),idx+1,perm)
        else:
            for d in neighbors[v]-set(perm.values()):
                walk(origin,v^(1<<d),idx+1,perm|{axis:d})
    for v in vertices:
        walk(v,v,0,{})
    return out

def canonical(path):
    w=labels(path)
    def normalize(seq):
        d={}
        return bytes(d.setdefault(v,len(d)) for v in seq)
    return min(normalize(w),normalize(reversed(w)))

def main():
    anchors=set(json.load(open("q9_junction_integer_audit/unbounded_duals/all66_17429_h0_n16.json"))["fixed"])
    chain=longest_component(anchors)
    seen=set()
    hits=[]
    for name in ["q9_onechord_expanded_800.txt","q9_port_all_new_plateau.txt"]:
        for row,s in enumerate(Path(name).read_text().splitlines()):
            p=list(map(int,s.split()))
            k=canonical(p)
            if k in seen:continue
            seen.add(k)
            copies=images_in_graph(set(p),chain,anchors)
            if copies:hits.append(dict(input=name,row=row,images=sorted(map(sorted,copies))))
    print(json.dumps(dict(total=len(seen),matched=len(hits),results=hits)))
if __name__=="__main__":main()
