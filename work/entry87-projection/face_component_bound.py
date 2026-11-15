"""Check the extremal seven-face witnesses and propagate component counts to eight dimensions."""
import argparse
from pathlib import Path
from solve import save

def count_components(occupied):
    graph={v:{v^(1<<j) for j in range(7)}&occupied for v in occupied}
    assert all(len(edges)<=2 for edges in graph.values())
    rest=set(occupied);count=0
    while rest:
        v=rest.pop();group={v};q=[v]
        while q:
            new=graph[q.pop()]&rest;rest-=new;group|=new;q.extend(new)
        assert sum(len(graph[w]) for w in group)==2*(len(group)-1)
        count+=1
    return count

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("input",type=Path);a=p.parse_args()
    minima={};algorithm2={};witnesses={}
    for line in a.input.read_text().splitlines():
        kind,*v=line.split()
        if kind not in ("seven","stream"):continue
        n,c,low,high=map(int,v);assert not (low>>64 or high>>64)
        sites={x for x in range(128) if (low|(high<<64))>>x&1}
        assert len(sites)==n and count_components(sites)==c
        if kind=="seven":algorithm2[n]=c
        else:minima[n]=c;witnesses[n]=sorted(sites)
    assert set(minima)==set(range(min(minima),65)) and all(minima[n]==c for n,c in algorithm2.items())
    def lower(n):return minima.get(n,2 if n>51 else int(n>0))
    rows=[]
    for m in range(2,129):
        pair=min(lower(j)+lower(m-j) for j in range(max(0,m-64),min(64,m)+1))
        if 8*pair>m+14:rows.append(dict(vertices=m,components_per_parallel_pair_at_least=pair,sum_at_least=8*pair,required=m+14))
    upper=min(r["vertices"] for r in rows)-1
    assert set(r["vertices"] for r in rows)==set(range(upper+1,129))
    save(Path("face-component-bound.json"),dict(input=a.input.name,seven_min_components=minima,witnesses=witnesses,
             excluded_eight_two_component_sizes=rows,eight_upper=upper,minimum_middle=193-upper))
    print("two-component upper",upper,"middle lower",193-upper,flush=True)
