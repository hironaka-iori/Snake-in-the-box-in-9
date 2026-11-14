"""Verify the exceptional free-order cases by elementary undirected degree rules."""
from parity_skeleton import structure
from solve import paths


def contradiction(vertices,split=None):
    ordered,adj,support,tips=structure(vertices)
    live={x:set(adj[x]) for x in ordered}
    live[-1]=set(tips)
    for x in tips:live[x].add(-1)
    forced={x:set() for x in live}
    if split is not None:
        a,b,chosen=split
        assert b in live[a]
        if chosen:
            forced[a].add(b);forced[b].add(a)
        else:
            live[a].remove(b);live[b].remove(a)
    while True:
        before=sum(map(len,live.values())),sum(map(len,forced.values()))
        for x in sorted(live):
            if len(live[x])<2 or len(forced[x])>2:
                return x,sorted(live[x]),sorted(forced[x])
            if len(live[x])==2:
                for y in live[x]:
                    forced[x].add(y);forced[y].add(x)
            if len(forced[x])==2:
                for y in live[x]-forced[x]:
                    live[x].remove(y);live[y].remove(x)
        after=sum(map(len,live.values())),sum(map(len,forced.values()))
        if before==after:return None


if __name__=="__main__":
    odd=sorted(paths()[1][1::2])
    assert contradiction(odd)[0]==436
    print("No edit:",contradiction(odd))
    odd.remove(69);odd.append(84)
    for chosen in (False,True):
        evidence=contradiction(odd,(22,28,chosen))
        assert evidence is not None
        print("69 replaced by 84; edge 22--28",chosen,evidence)
