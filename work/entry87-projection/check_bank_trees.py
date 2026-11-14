"""Replay terminal degree/cycle claims via independent Hamming-distance incidence."""
import json
from pathlib import Path
from bank_parity import inputs


def graph(anchors,parity,endcaps=None):
    if endcaps is None:endcaps=bool(parity)
    labels=sorted(anchors)
    n=len(labels);adj=[set() for _ in range(n+1)]
    def add(i,j):adj[i].add(j);adj[j].add(i)
    for w in range(512):
        if w.bit_count()%2==parity:continue
        neighbors=[i for i,x in enumerate(labels) if (w^x).bit_count()==1]
        if len(neighbors)==2:add(*neighbors)
        elif len(neighbors)==1 and endcaps:add(n,neighbors[0])
    if not endcaps:
        for i in range(n):add(n,i)
    return adj,[set() for _ in adj]


def verify(live,used,tree):
    while True:
        before=sum(map(len,live)),sum(map(len,used))
        for v in range(len(live)):
            if len(live[v])<2 or len(used[v])>2:
                assert tree[0] in ("few","many","cycle"),tree[0]
                return 1
            if len(live[v])==2:
                for w in live[v]:
                    used[v].add(w);used[w].add(v)
            elif len(used[v])==2:
                for w in live[v]-used[v]:
                    live[v].remove(w);live[w].remove(v)
        if before==(sum(map(len,live)),sum(map(len,used))):break
    if tree[0]=="cycle":
        component=set(tree[1]);reached=set();stack=[min(component)]
        while stack:
            v=stack.pop()
            if v in reached:continue
            reached.add(v);stack.extend(used[v]-reached)
        assert reached==component and 0<len(component)<len(live) and all(len(used[v])==2 for v in component)
        return 1
    assert tree[0]=="split"
    _,x,y,absent,present=tree
    assert y in live[x]-used[x]
    a=[z.copy() for z in live];b=[z.copy() for z in used]
    a[x].remove(y);a[y].remove(x)
    b[x].add(y);b[y].add(x)
    return 1+verify(a,[z.copy() for z in used],absent)+verify([z.copy() for z in live],b,present)


if __name__=="__main__":
    import sys
    path=Path(sys.argv[1]);proofs=json.loads(path.read_text())
    inputs_by_id=dict(inputs())
    total=0
    for p in proofs:
        parity=p["parity"];e=p["edit"];k=len(e)//2
        anchors=set(inputs_by_id[p["index"]][parity::2])-set(e[:k])|set(e[k:])
        count=verify(*graph(anchors,parity),p["tree"])
        assert count==p["nodes"];total+=count
    print("verified",len(proofs),"trees and",total,"nodes")
