"""Find one-dimensional obstructions and necessary complementary endpoint paths."""
import argparse,json
from collections import Counter,deque
from pathlib import Path
from bank_parity import inputs
from solve import BANK,BANK_HASH,sha256,defects,save
from syndrome import neighbour_syndrome


def report(path):
    S=set(path);Y=neighbour_syndrome(S);X=S&Y
    assert len(S)==len(path) and neighbour_syndrome(Y)==S
    graph={v:{v^(1<<b) for b in range(9)}&Y for v in Y}
    odd={v for v in Y if len(graph[v])%2}
    assert odd==X
    remain=set(Y);comps=[]
    while remain:
        v=remain.pop();C={v};q=[v]
        while q:
            new=graph[q.pop()]&remain;remain-=new;C|=new;q.extend(new)
        assert len(C&X)%2==0
        comps.append(C)
    distance=None;shortest=None
    if len(X)==2:
        a,b=sorted(X);parent={a:None};q=deque([a])
        while q and b not in parent:
            v=q.popleft()
            for n in sorted(graph[v]-parent.keys()):q.append(n);parent[n]=v
        shortest=[b]
        while shortest[-1]!=a:shortest.append(parent[shortest[-1]])
        shortest.reverse();distance=len(shortest)-1
        assert not defects(shortest) and not (set(shortest[1:-1])&S)
    return dict(selected=len(S),syndrome_size=len(Y),intersection=sorted(X),
                component_sizes=sorted(map(len,comps)),endpoint_distance=distance,
                shortest=shortest)


if __name__=="__main__":
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    family=[r["vertex_sequence"] for r in json.loads(raw)]
    bank=[]
    for q in family:
        assert not defects(q)
        r=report(q);assert set(r["intersection"])=={q[0],q[-1]}
        bank.append(r)
    near=[]
    for i,q in inputs():
        r=report(q);near.append(r)
    save(Path("dual-endpoints.json"),dict(source=bank,one_chord=near))
    print(Counter(r["endpoint_distance"] for r in bank),Counter(len(r["intersection"]) for r in near))
