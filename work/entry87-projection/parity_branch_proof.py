"""Independent exact cycle check for the four hardest two-replacement anchor sets."""
from itertools import combinations
import json
from pathlib import Path
from parity_skeleton import structure
from solve import paths,save


def state(vertices):
    order,adj,support,tips=structure(vertices)
    live={x:set(adj[x]) for x in order}
    live[-1]=set(tips)
    for x in tips:live[x].add(-1)
    return live,{x:set() for x in live}


def reason(live,must):
    while True:
        before=sum(map(len,live.values())),sum(map(len,must.values()))
        for x in sorted(live):
            if len(live[x])<2 or len(must[x])>2:
                return dict(kind="degree",vertex=x,permitted=sorted(live[x]),forced=sorted(must[x]))
            if len(live[x])==2:
                for y in live[x]-must[x]:
                    must[x].add(y);must[y].add(x)
            if len(must[x])==2:
                for y in live[x]-must[x]:
                    live[x].remove(y);live[y].remove(x)
        # Every component of the forced edges has degree <=2 unless the next
        # pass exposes an immediate degree contradiction. Detect closed components.
        unseen=set(must)
        while unseen:
            root=min(unseen);unseen.remove(root)
            seen={root};stack=[root]
            while stack:
                neighbours=must[stack.pop()]&unseen
                seen|=neighbours;unseen-=neighbours;stack.extend(neighbours)
            if len(seen)<len(live) and all(len(must[x])==2 for x in seen):
                return dict(kind="proper cycle",vertices=sorted(seen))
        if before==(sum(map(len,live.values())),sum(map(len,must.values()))):
            return None


def refute(live,must):
    terminal=reason(live,must)
    if terminal:return terminal
    candidates=[(len(live[x])-len(must[x]),x) for x in live if must[x]!=live[x]]
    if not candidates:raise ValueError("surviving Hamilton cycle")
    _,x=min(candidates)
    a,b=(22,28) if 28 in live[22]-must[22] else (x,min(live[x]-must[x]))
    proof=dict(kind="split",edge=[a,b],branches=[])
    for present in (False,True):
        next_live={x:set(ns) for x,ns in live.items()}
        next_must={x:set(ns) for x,ns in must.items()}
        if present:
            next_must[a].add(b);next_must[b].add(a)
        else:
            next_live[a].remove(b);next_live[b].remove(a)
        proof["branches"].append(refute(next_live,next_must))
    return proof


def size(tree):
    return 1+sum(size(child) for child in tree.get("branches",[]))


if __name__=="__main__":
    odd=set(paths()[1][1::2]);certificates=[]
    for f in sorted(Path().glob("two-parity-1-*-all.json")):
        for a,b,x,y,result in json.loads(f.read_text())["details"]:
            if result!="Hamilton path infeasible":continue
            anchors=sorted(odd-{a,b}|{x,y})
            proof=refute(*state(anchors))
            print(a,b,x,y,size(proof))
            certificates.append(dict(change=[a,b,x,y],tree=proof))
    assert len(certificates)==4
    save(Path("two-parity-exceptional.json"),certificates)
